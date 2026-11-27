#!/usr/bin/env python3
"""Problem-agnostic verifier for strict RFC-8259 JSON search artifacts & SHA-256 determinism.

Validates Track B (`Disprove/` + `search/`) JSON sweep logs and runner outputs:
- Rejects non-RFC-8259 constants (`NaN`, `Infinity`, `-Infinity`) via `loads_strict_json`.
- Verifies `deterministic_sha256 == canonical_sha256(data["canonical"])`.
- Provides `assert_deterministic_pair` to confirm multi-thread (`t=1 == t=N`) bit-for-bit parity.
"""

from __future__ import annotations

import argparse
import pathlib
import sys
import tempfile
from typing import Any

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from native_cache import (  # type: ignore  # noqa: E402
    canonical_sha256,
    dump_strict_json,
    loads_strict_json,
)


def verify_artifact_payload(data: Any, *, require_canonical_sha256: bool = True) -> str | None:
    """Validate a parsed JSON artifact dict and return its verified `deterministic_sha256`."""
    if not isinstance(data, dict):
        raise ValueError(f"Expected top-level JSON object, got {type(data).__name__}")
    # Re-validate strict RFC-8259 serializability on in-memory objects too.
    canonical_sha256(data)

    has_sha = "deterministic_sha256" in data
    if require_canonical_sha256 and not has_sha:
        raise ValueError("Missing required `deterministic_sha256` field")
    if not has_sha:
        return None

    if "canonical" not in data:
        raise ValueError("Missing `canonical` payload required alongside `deterministic_sha256`")
    expected = canonical_sha256(data["canonical"])
    actual = data["deterministic_sha256"]
    if not isinstance(actual, str) or actual != expected:
        raise ValueError(f"deterministic_sha256 mismatch: expected {expected}, got {actual!r}")
    return actual


def verify_artifact_file(path: pathlib.Path, *, require_canonical_sha256: bool = True) -> str | None:
    """Load `path` as strict RFC-8259 JSON and verify its `deterministic_sha256` digest."""
    raw = path.read_text(encoding="utf-8")
    data = loads_strict_json(raw)
    return verify_artifact_payload(data, require_canonical_sha256=require_canonical_sha256)


def assert_deterministic_pair(payload_a: dict[str, Any], payload_b: dict[str, Any]) -> str:
    """Verify two run payloads (e.g. `t=1` vs `t=N`) match bit-for-bit on `deterministic_sha256`."""
    sha_a = verify_artifact_payload(payload_a, require_canonical_sha256=True)
    sha_b = verify_artifact_payload(payload_b, require_canonical_sha256=True)
    if sha_a is None or sha_b is None:
        raise ValueError("Expected non-null deterministic_sha256 digests from both payloads")
    if sha_a != sha_b:
        raise AssertionError(f"Non-deterministic canonical digest across runs: {sha_a} != {sha_b}")
    return sha_a


def run_self_test() -> int:
    """Exercise strict JSON, canonical SHA-256 tamper detection, and pair determinism checks."""
    with tempfile.TemporaryDirectory(prefix="verify_json_selftest_") as tmp:
        root = pathlib.Path(tmp)
        canon_a = {"bound": 1000, "hits": [], "meta": {"threads": 1, "mode": "sweep"}}
        canon_b = {"meta": {"mode": "sweep", "threads": 1}, "hits": [], "bound": 1000}
        digest = canonical_sha256(canon_a)

        artifact_1 = {"canonical": canon_a, "deterministic_sha256": digest, "telemetry": {"elapsed_s": 0.1}}
        artifact_n = {"canonical": canon_b, "deterministic_sha256": digest, "telemetry": {"elapsed_s": 0.03}}

        p1 = root / "run_t1.json"
        pn = root / "run_t4.json"
        dump_strict_json(artifact_1, p1)
        dump_strict_json(artifact_n, pn)

        if verify_artifact_file(p1) != digest:
            raise AssertionError("verify_artifact_file returned unexpected digest")
        if assert_deterministic_pair(artifact_1, artifact_n) != digest:
            raise AssertionError("assert_deterministic_pair failed on key-reordered equivalent payloads")

        tampered = root / "tampered.json"
        dump_strict_json(
            {"canonical": {"bound": 1001, "hits": []}, "deterministic_sha256": digest},
            tampered,
        )
        try:
            verify_artifact_file(tampered)
            raise AssertionError("Failed to reject tampered canonical payload")
        except ValueError:
            pass

        nan_file = root / "nan.json"
        nan_file.write_text('{"canonical": {"x": NaN}, "deterministic_sha256": "0"}\n', encoding="utf-8")
        try:
            verify_artifact_file(nan_file)
            raise AssertionError("Failed to reject non-RFC-8259 NaN JSON")
        except ValueError:
            pass

    print("PASS: search/verify_json_artifacts.py self-test passed (strict RFC-8259 & SHA-256 determinism).")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify strict RFC-8259 JSON search artifacts and deterministic SHA-256 digests"
    )
    parser.add_argument("paths", nargs="*", type=pathlib.Path, help="JSON artifact files or directories to verify")
    parser.add_argument("--self-test", action="store_true", help="Run built-in unit self-tests")
    parser.add_argument(
        "--allow-missing-sha",
        action="store_true",
        help="Only enforce canonical_sha256 when deterministic_sha256 is present",
    )
    args = parser.parse_args()
    if args.self_test:
        return run_self_test()

    targets: list[pathlib.Path] = []
    for item in args.paths:
        if item.is_dir():
            targets.extend(sorted(item.rglob("*.json")))
        else:
            targets.append(item)

    if not targets:
        print("PASS: No JSON search artifacts to verify.")
        return 0

    failed = 0
    for path in targets:
        try:
            verify_artifact_file(path, require_canonical_sha256=not args.allow_missing_sha)
        except (ValueError, OSError) as exc:
            print(f"FAIL: {path}: {exc}", file=sys.stderr)
            failed += 1
    if failed:
        return 1
    print(f"PASS: Verified {len(targets)} strict RFC-8259 JSON artifact(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
