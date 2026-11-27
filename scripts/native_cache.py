#!/usr/bin/env python3
"""Zero-dependency content-hashed native binary cache & strict RFC-8259 JSON helper.

Designed for Track B (`Disprove/` + `search/`) compiled search engines (C/C++/Rust/CUDA):
- `cached_binary_path(prefix, source_paths, suffix="", cache_dir="/tmp")`:
  Hashes all source/header files via SHA-256 into `<cache_dir>/<prefix>_<sha12><suffix>`,
  eliminating stale-binary collisions across worktrees, branches, and edited headers.
- `atomic_compile(cmd, dst_path, ...)`:
  Compiles into a unique PID+nonce temporary file in `dst_path.parent` and `os.replace()`s
  atomically, eliminating partial-binary races when parallel processes compile concurrently.
- `dump_strict_json(obj, path)` / `loads_strict_json(raw)` / `canonical_sha256(obj)`:
  Enforces strict RFC-8259 JSON (`allow_nan=False`, rejecting `NaN`/`Infinity`/`-Infinity`)
  with atomic writes and deterministic SHA-256 digests over canonical payloads.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable, Mapping, Sequence
import concurrent.futures
import hashlib
import json
import os
import pathlib
import secrets
import shutil
import subprocess
import sys
import tempfile
from typing import Any


DEFAULT_SOURCE_EXTENSIONS = frozenset(
    {".c", ".h", ".cc", ".cpp", ".cxx", ".hpp", ".hh", ".rs", ".cu", ".cuh"}
)
DEFAULT_SOURCE_FILENAMES = frozenset({"Cargo.toml", "Cargo.lock"})


def _collect_source_files(
    source_paths: Iterable[str | os.PathLike[str]] | str | os.PathLike[str],
) -> list[tuple[str, pathlib.Path]]:
    if isinstance(source_paths, (str, os.PathLike)):
        items: list[str | os.PathLike[str]] = [source_paths]
    else:
        items = list(source_paths)

    collected: dict[pathlib.Path, str] = {}
    explicit_files: list[pathlib.Path] = []
    for raw in items:
        p = pathlib.Path(raw)
        if not p.exists():
            raise FileNotFoundError(f"Source path does not exist: {p}")
        if p.is_file():
            explicit_files.append(p)
        elif p.is_dir():
            for child in sorted(p.rglob("*")):
                if not child.is_file():
                    continue
                if any(part.startswith(".") or part == "target" for part in child.relative_to(p).parts):
                    continue
                if (
                    child.suffix.lower() in DEFAULT_SOURCE_EXTENSIONS
                    or child.name in DEFAULT_SOURCE_FILENAMES
                ):
                    collected[child.resolve()] = child.relative_to(p).as_posix()
        else:
            raise ValueError(f"Unsupported source path type: {p}")

    if explicit_files:
        resolved_explicit = [f.resolve() for f in explicit_files]
        unique_explicit = set(resolved_explicit)
        common_root: pathlib.Path | None = None
        if len(unique_explicit) > 1:
            try:
                common_root = pathlib.Path(os.path.commonpath([str(f) for f in unique_explicit]))
            except ValueError:
                common_root = None
        for orig, resolved in zip(explicit_files, resolved_explicit):
            if common_root is not None:
                label = resolved.relative_to(common_root).as_posix()
            else:
                label = orig.name
            collected.setdefault(resolved, label)

    if not collected:
        raise ValueError("No source files resolved from source_paths")
    return sorted(((label, path) for path, label in collected.items()), key=lambda pair: (pair[0], str(pair[1])))


def cached_binary_path(
    prefix: str,
    source_paths: Iterable[str | os.PathLike[str]] | str | os.PathLike[str],
    suffix: str = "",
    cache_dir: str | os.PathLike[str] = "/tmp",
) -> pathlib.Path:
    """Return a content-hashed binary path `<cache_dir>/<prefix>_<sha12><suffix>`."""
    if not prefix or "/" in prefix or "\\" in prefix or ".." in prefix:
        raise ValueError(f"Invalid binary cache prefix: {prefix!r}")

    files = _collect_source_files(source_paths)
    h = hashlib.sha256()
    for label, path in files:
        data = path.read_bytes()
        h.update(label.encode("utf-8"))
        h.update(b"\0")
        h.update(str(len(data)).encode("ascii"))
        h.update(b"\0")
        h.update(data)
        h.update(b"\0")
    digest = h.hexdigest()[:12]
    return pathlib.Path(cache_dir) / f"{prefix}_{digest}{suffix}"


def _prepare_compile_cmd(
    cmd: Sequence[str | os.PathLike[str]],
    dst: pathlib.Path,
    tmp_bin: pathlib.Path,
) -> list[str]:
    str_cmd = [os.fspath(arg) for arg in cmd]
    dst_str = os.fspath(dst)
    tmp_str = os.fspath(tmp_bin)
    replaced = False
    out_cmd: list[str] = []
    for arg in str_cmd:
        if "{out}" in arg:
            out_cmd.append(arg.replace("{out}", tmp_str))
            replaced = True
        elif arg == dst_str:
            out_cmd.append(tmp_str)
            replaced = True
        else:
            out_cmd.append(arg)
    if not replaced:
        out_cmd.extend(["-o", tmp_str])
    return out_cmd


def atomic_compile(
    cmd: Sequence[str | os.PathLike[str]],
    dst_path: str | os.PathLike[str],
    *,
    force: bool = False,
    cwd: str | os.PathLike[str] | None = None,
    env: Mapping[str, str] | None = None,
) -> pathlib.Path:
    """Compile into a PID/nonce temp file and atomically replace `dst_path` via `os.replace()`."""
    dst = pathlib.Path(dst_path)
    if not force and dst.exists():
        return dst

    dst.parent.mkdir(parents=True, exist_ok=True)
    tmp_bin = dst.parent / f".{dst.name}.tmp.{os.getpid()}.{secrets.token_hex(6)}"
    resolved_cmd = _prepare_compile_cmd(cmd, dst, tmp_bin)
    try:
        res = subprocess.run(
            resolved_cmd,
            capture_output=True,
            text=True,
            check=False,
            cwd=cwd,
            env=dict(env) if env is not None else None,
        )
        if res.returncode != 0:
            raise RuntimeError(
                f"Compilation failed ({res.returncode}): {' '.join(resolved_cmd)}\n{res.stderr}"
            )
        if not tmp_bin.exists():
            raise RuntimeError(
                f"Compiler exited 0 without producing expected output file: {tmp_bin}"
            )
        os.replace(tmp_bin, dst)
    finally:
        tmp_bin.unlink(missing_ok=True)
    return dst


def _reject_non_rfc8259(token: str) -> None:
    raise ValueError(f"Non-RFC-8259 JSON constant rejected: {token}")


def loads_strict_json(raw: str) -> Any:
    """Parse JSON strictly rejecting `NaN`, `Infinity`, and `-Infinity`."""
    data = json.loads(raw, parse_constant=_reject_non_rfc8259)
    json.dumps(data, allow_nan=False)
    return data


def dump_strict_json(
    obj: Any,
    path: str | os.PathLike[str],
    *,
    indent: int | None = 2,
    sort_keys: bool = False,
) -> pathlib.Path:
    """Atomically write strict RFC-8259 JSON (`allow_nan=False`) to `path`."""
    serialized = json.dumps(obj, indent=indent, sort_keys=sort_keys, allow_nan=False) + "\n"
    dst = pathlib.Path(path)
    dst.parent.mkdir(parents=True, exist_ok=True)
    tmp_json = dst.parent / f".{dst.name}.tmp.{os.getpid()}.{secrets.token_hex(6)}"
    try:
        tmp_json.write_text(serialized, encoding="utf-8")
        os.replace(tmp_json, dst)
    finally:
        tmp_json.unlink(missing_ok=True)
    return dst


def canonical_sha256(obj: Any) -> str:
    """Compute a deterministic SHA-256 hex digest over strict canonical RFC-8259 JSON."""
    encoded = json.dumps(obj, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def run_self_test() -> int:
    """Verify content hashing, atomic compilation, concurrency safety, and RFC-8259 JSON."""
    with tempfile.TemporaryDirectory(prefix="native_cache_selftest_") as tmp:
        root = pathlib.Path(tmp)
        wt1 = root / "wt1"
        wt2 = root / "wt2"
        cache = root / "cache"
        wt1.mkdir()
        wt2.mkdir()
        cache.mkdir()

        c1 = wt1 / "solver.c"
        h1 = wt1 / "solver.h"
        c2 = wt2 / "solver.c"
        h2 = wt2 / "solver.h"

        h_src = "#define ANSWER 42\n"
        c_src = '#include "solver.h"\nint main(void) { return ANSWER == 42 ? 0 : 1; }\n'
        h1.write_text(h_src, encoding="utf-8")
        c1.write_text(c_src, encoding="utf-8")
        h2.write_text(h_src, encoding="utf-8")
        c2.write_text(c_src, encoding="utf-8")

        bin1 = cached_binary_path("test_solver", [c1, h1], cache_dir=cache)
        bin2 = cached_binary_path("test_solver", [h2, c2], cache_dir=cache)
        if bin1 != bin2:
            raise AssertionError(f"Cross-worktree cache hash mismatch: {bin1} != {bin2}")

        bin_dir = cached_binary_path("test_solver", [wt1], suffix="_asan", cache_dir=cache)
        if not bin_dir.name.endswith("_asan") or bin_dir.name.removesuffix("_asan") != bin1.name:
            raise AssertionError(f"Directory/suffix hash mismatch: {bin_dir} vs {bin1}")

        h1.write_text("#define ANSWER 43\n", encoding="utf-8")
        bin_modified = cached_binary_path("test_solver", [c1, h1], cache_dir=cache)
        if bin_modified == bin1:
            raise AssertionError("Header modification failed to invalidate content hash")
        h1.write_text(h_src, encoding="utf-8")

        # Test duplicate basenames across subdirectories preserve relative path context.
        for wt in (wt1, wt2):
            (wt / "a").mkdir()
            (wt / "b").mkdir()
            (wt / "a" / "util.c").write_text("int util_a(void) { return 1; }\n", encoding="utf-8")
            (wt / "b" / "util.c").write_text("int util_b(void) { return 2; }\n", encoding="utf-8")
        dup1 = cached_binary_path("dup_test", [wt1 / "a" / "util.c", wt1 / "b" / "util.c"], cache_dir=cache)
        dup2 = cached_binary_path("dup_test", [wt2 / "b" / "util.c", wt2 / "a" / "util.c"], cache_dir=cache)
        if dup1 != dup2:
            raise AssertionError(f"Duplicate-basename cross-worktree mismatch: {dup1} != {dup2}")
        (wt1 / "a" / "util.c").write_text("int util_b(void) { return 2; }\n", encoding="utf-8")
        (wt1 / "b" / "util.c").write_text("int util_a(void) { return 1; }\n", encoding="utf-8")
        dup_swapped = cached_binary_path("dup_test", [wt1 / "a" / "util.c", wt1 / "b" / "util.c"], cache_dir=cache)
        if dup_swapped == dup1:
            raise AssertionError("Swapping contents across duplicate-basename paths failed to change hash")

        # Test Rust crate directory scanning includes Cargo.toml and Cargo.lock (while ignoring target/).
        crate = root / "rust_crate"
        (crate / "src").mkdir(parents=True)
        (crate / "target" / "debug").mkdir(parents=True)
        (crate / "src" / "main.rs").write_text("fn main() {}\n", encoding="utf-8")
        (crate / "Cargo.toml").write_text('[package]\nname = "demo"\nversion = "0.1.0"\n', encoding="utf-8")
        (crate / "Cargo.lock").write_text('version = 3\n', encoding="utf-8")
        (crate / "target" / "debug" / "junk.rs").write_text("ignored\n", encoding="utf-8")
        rust_bin1 = cached_binary_path("rust_demo", [crate], cache_dir=cache)
        (crate / "Cargo.toml").write_text('[package]\nname = "demo"\nversion = "0.2.0"\n', encoding="utf-8")
        rust_bin2 = cached_binary_path("rust_demo", [crate], cache_dir=cache)
        if rust_bin2 == rust_bin1:
            raise AssertionError("Cargo.toml edit failed to invalidate Rust crate directory hash")
        (crate / "Cargo.lock").write_text('version = 4\n', encoding="utf-8")
        rust_bin3 = cached_binary_path("rust_demo", [crate], cache_dir=cache)
        if rust_bin3 == rust_bin2:
            raise AssertionError("Cargo.lock edit failed to invalidate Rust crate directory hash")

        # Test atomic_compile with Python-emulated compiler (and real cc if available).
        py_out = cache / "py_tool"
        py_cmd = [
            sys.executable,
            "-c",
            "import pathlib, sys; p = pathlib.Path(sys.argv[1]); p.write_text('ok\\n'); p.chmod(0o755)",
            "{out}",
        ]
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
            futs = [pool.submit(atomic_compile, py_cmd, py_out, force=True) for _ in range(4)]
            for fut in futs:
                fut.result()
        if py_out.read_text(encoding="utf-8") != "ok\n":
            raise AssertionError("Concurrent atomic_compile produced unexpected output")

        # Test failure cleanup leaves no temp files or stale partial binary.
        fail_out = cache / "fail_tool"
        fail_cmd = [sys.executable, "-c", "import pathlib, sys; pathlib.Path(sys.argv[1]).write_text('partial'); sys.exit(2)", "{out}"]
        try:
            atomic_compile(fail_cmd, fail_out)
            raise AssertionError("Expected RuntimeError from failing compiler command")
        except RuntimeError:
            pass
        if fail_out.exists():
            raise AssertionError("Failed atomic_compile created destination file")

        cc = shutil.which("cc") or shutil.which("gcc")
        if cc:
            c_bin = atomic_compile([cc, "-O2", "-Wall", "-Wextra", "-Werror", str(c1)], bin1)
            res = subprocess.run([str(c_bin)], capture_output=True, text=True, check=False)
            if res.returncode != 0:
                raise AssertionError(f"Compiled C self-test binary exited with {res.returncode}")
            # Second call should reuse cached binary without recompiling.
            atomic_compile(["/nonexistent/compiler", str(c1)], bin1, force=False)

        leftover_tmps = [p for p in cache.iterdir() if ".tmp." in p.name]
        if leftover_tmps:
            raise AssertionError(f"Leftover temporary files after atomic_compile: {leftover_tmps}")

        # Test strict RFC-8259 JSON enforcement & deterministic digest.
        json_path = root / "out" / "strict.json"
        dump_strict_json({"b": [1, 2], "a": "ok"}, json_path)
        loaded = loads_strict_json(json_path.read_text(encoding="utf-8"))
        if loaded != {"b": [1, 2], "a": "ok"}:
            raise AssertionError(f"JSON round-trip mismatch: {loaded}")
        if canonical_sha256({"a": 1, "b": 2}) != canonical_sha256({"b": 2, "a": 1}):
            raise AssertionError("canonical_sha256 is not key-order invariant")

        for bad_val in (float("nan"), float("inf"), float("-inf")):
            try:
                dump_strict_json({"bad": bad_val}, json_path)
                raise AssertionError(f"dump_strict_json failed to reject {bad_val!r}")
            except ValueError:
                pass
            try:
                canonical_sha256({"bad": bad_val})
                raise AssertionError(f"canonical_sha256 failed to reject {bad_val!r}")
            except ValueError:
                pass
        for bad_raw in ('{"x": NaN}', '{"x": Infinity}', '{"x": -Infinity}'):
            try:
                loads_strict_json(bad_raw)
                raise AssertionError(f"loads_strict_json failed to reject {bad_raw}")
            except ValueError:
                pass

    print("PASS: scripts/native_cache.py self-test passed (content-hash, atomic compile, strict RFC-8259 JSON).")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Content-hashed native binary cache & strict JSON helper")
    parser.add_argument("--self-test", action="store_true", help="Run built-in unit self-tests")
    args = parser.parse_args()
    if args.self_test:
        return run_self_test()
    parser.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
