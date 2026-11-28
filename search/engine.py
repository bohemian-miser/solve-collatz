#!/usr/bin/env python3
"""Shared harness for compiled off-kernel search engines (Track B).

Every engine in `search/` follows the same contract, which this module implements once:

- `compile_c(prefix, source)` builds a C11 engine into a content-hashed `/tmp` path with the
  standard strict flags (`-Wall -Wextra -Werror -std=c11 -pthread`), or an ASan+UBSan build
  with `asan=True`. Nothing is written to the working tree.
- `run_json_engine(binary, args)` runs the engine, which must print strict RFC-8259 JSON with a
  `canonical` object on stdout (everything that must be reproducible goes in `canonical`;
  timing and thread counts go outside it). Returns the parsed JSON with `deterministic_sha256`
  set to the hash of `canonical`.
- `check_thread_determinism(run)` runs `run(threads)` for 1 and N threads and fails unless the
  `deterministic_sha256` values match.

See `search/example_engine/` for a complete engine with its self-test.
"""

from __future__ import annotations

import pathlib
import subprocess
import sys
from typing import Any, Callable, Iterable, Sequence

SEARCH_DIR = pathlib.Path(__file__).resolve().parent
SCRIPTS_DIR = SEARCH_DIR.parent / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from native_cache import atomic_compile, cached_binary_path, canonical_sha256, loads_strict_json  # noqa: E402

C11_FLAGS = ("-Wall", "-Wextra", "-Werror", "-std=c11", "-pthread")
ASAN_FLAGS = ("-g", "-fsanitize=address,undefined", "-fno-omit-frame-pointer")


def compile_c(
    prefix: str,
    source: pathlib.Path,
    *,
    hash_paths: Iterable[pathlib.Path] | None = None,
    asan: bool = False,
    force: bool = False,
    libs: Sequence[str] = ("-lm",),
) -> pathlib.Path:
    """Compile `source` to `/tmp/<prefix>_<sha12>[_asan]`; `hash_paths` defaults to `[source]`.

    Pass the engine's directory as `hash_paths` when it `#include`s local headers, so editing a
    header triggers a rebuild.
    """
    if not source.exists():
        raise FileNotFoundError(f"Missing C source: {source}")
    suffix = "_asan" if asan else ""
    target = cached_binary_path(prefix, list(hash_paths or [source]), suffix=suffix)
    cmd = ["gcc", "-O2" if asan else "-O3", *C11_FLAGS]
    if asan:
        cmd.extend(ASAN_FLAGS)
    cmd.extend([str(source), *libs, "-o", "{out}"])
    return atomic_compile(cmd, target, force=force)


def run_json_engine(
    binary: pathlib.Path,
    args: Sequence[str],
    *,
    ok_returncodes: Sequence[int] = (0,),
) -> dict[str, Any]:
    """Run `binary args`, parse its strict-JSON stdout and attach `deterministic_sha256`."""
    res = subprocess.run([str(binary), *args], capture_output=True, text=True, check=False)
    if res.returncode not in ok_returncodes:
        raise RuntimeError(f"{binary.name} exited with {res.returncode}:\n{res.stderr}")
    data = loads_strict_json(res.stdout)
    if not isinstance(data, dict) or not isinstance(data.get("canonical"), dict):
        raise ValueError(f"{binary.name} output has no `canonical` object")
    data["deterministic_sha256"] = canonical_sha256(data["canonical"])
    return data


def check_thread_determinism(
    run: Callable[[int], dict[str, Any]],
    threads: Sequence[int] = (1, 4),
) -> str:
    """Return the shared `deterministic_sha256` of `run(t)` for each `t`, or raise on mismatch."""
    shas = {t: run(t)["deterministic_sha256"] for t in threads}
    if len(set(shas.values())) != 1:
        raise AssertionError(f"Thread nondeterminism: {shas}")
    return next(iter(shas.values()))
