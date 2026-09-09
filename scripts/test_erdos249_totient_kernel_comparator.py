#!/usr/bin/env python3
"""Non-Lean unit checks for the dedicated #249 Comparator receipt gate."""

import importlib.util
from pathlib import Path

SCRIPT = Path(__file__).with_name("write_erdos249_totient_kernel_comparator_receipt.py")
SPEC = importlib.util.spec_from_file_location("receipt", SCRIPT)
assert SPEC and SPEC.loader
receipt = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(receipt)


def main() -> int:
    assert receipt.negative_is_semantic(1, receipt.EXPECTED_MISMATCH)
    assert not receipt.negative_is_semantic(0, receipt.EXPECTED_MISMATCH)
    assert not receipt.negative_is_semantic(124, receipt.EXPECTED_MISMATCH)
    assert not receipt.negative_is_semantic(125, receipt.EXPECTED_MISMATCH)
    assert not receipt.negative_is_semantic(1, "unrelated elaboration failure")
    print("#249 dedicated Comparator receipt semantics: pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
