#!/usr/bin/env python3
"""Finite checks for Type B r4 signed finite-period / cover-moment claims.

--quick (default): 2/5 counterexample, failed integer coefficients,
Phi_6(2)=3 with ord_9(2)=6, a handful of signed supports, Psi gauge,
and one divisor-cube numerical inequality. Does not enumerate Type B's
32800 signed cases. No sympy.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from fractions import Fraction
from math import gcd
from pathlib import Path

RECEIPT_DIR = Path(
    "public-source-redacted://state/type_b_return_batches/"
    "erdos_revision_packets_r4_20260907/work/erdos_257"
)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def pow_mod(b: int, e: int, m: int) -> int:
    return pow(b, e, m)


def order_mod(b: int, m: int) -> int:
    if gcd(b, m) != 1:
        raise ValueError(f"gcd({b},{m}) != 1")
    x = 1 % m
    for k in range(1, m + 1):
        x = (x * b) % m
        if x == 1:
            return k
    raise RuntimeError(f"no order for {b} mod {m}")


def mu(n: int) -> int:
    if n == 1:
        return 1
    factors = 0
    x = n
    p = 2
    while p * p <= x:
        if x % p == 0:
            factors += 1
            x //= p
            if x % p == 0:
                return 0
        p += 1 if p == 2 else 2
    if x > 1:
        factors += 1
    return -1 if factors % 2 else 1


def phi_eval(n: int, b: int) -> int:
    """Phi_n(b) via prod_{d|n} (b^d-1)^{mu(n/d)}."""
    num, den = 1, 1
    d = 1
    while d * d <= n:
        if n % d == 0:
            for dd in {d, n // d}:
                m = mu(n // dd)
                term = b**dd - 1
                if m == 1:
                    num *= term
                elif m == -1:
                    den *= term
        d += 1
    return num // den


def finite_mersenne_sum(F: list[int], signs: list[int], b: int = 2) -> Fraction:
    s = Fraction(0)
    for n, eps in zip(F, signs):
        s += eps * Fraction(1, b**n - 1)
    return s


def psi(t: float) -> float:
    if t <= 0:
        return 0.0
    if t <= 4:
        return t
    u = math.log(t, 2)
    return (u**u) / ((u - 1) ** (u - 1))


def check_quick() -> dict:
    rows: list[dict] = []

    s = finite_mersenne_sum([2, 4], [1, 1], 2)
    rows.append(
        {
            "id": "two_fifths",
            "ok": s == Fraction(2, 5) and s.denominator == 5 and is_prime(5)
            and not any(5 + 1 == 2**e for e in range(20)),
            "value": str(s),
        }
    )

    bad = Fraction(1, 2**1 - 1) + 3 * Fraction(1, 2**2 - 1)
    rows.append(
        {
            "id": "integer_coeff_collapse",
            "ok": bad == 2 and bad.denominator == 1,
            "value": str(bad),
        }
    )

    phi6 = phi_eval(6, 2)
    rows.append(
        {
            "id": "phi6_of_2",
            "ok": phi6 == 3,
            "value": phi6,
        }
    )
    rows.append(
        {
            "id": "ord_9_of_2",
            "ok": order_mod(2, 9) == 6,
            "value": order_mod(2, 9),
        }
    )
    rows.append(
        {
            "id": "ord_21_of_2",
            "ok": order_mod(2, 21) == 6,
            "value": order_mod(2, 21),
            "note": "order 6 is not only from 9; modulus 21 also has order 6",
        }
    )

    signed_ok = True
    signed_samples = []
    for F, signs in (
        ([1], [1]),
        ([1], [-1]),
        ([2, 3], [1, -1]),
        ([2, 6], [1, 1]),
        ([2, 3, 6], [1, -1, 1]),
        ([4, 6], [-1, -1]),
    ):
        val = finite_mersenne_sum(F, signs, 2)
        from math import lcm as math_lcm

        L = 1
        for n in F:
            L = math_lcm(L, n)
        D = val.denominator
        ordD = 1 if D == 1 else order_mod(2, D)
        ok = val != 0 and gcd(2, D) == 1 and ordD == L
        signed_ok = signed_ok and ok
        signed_samples.append({"F": F, "signs": signs, "val": str(val), "ord": ordD, "L": L, "ok": ok})
    rows.append({"id": "signed_small_supports", "ok": signed_ok, "samples": signed_samples})

    psi_ok = (
        abs(psi(1) - 1) < 1e-12
        and abs(psi(4) - 4) < 1e-12
        and abs(psi(16) - (4**4) / (3**3)) < 1e-9
    )
    rows.append({"id": "psi_gauge", "ok": psi_ok, "psi16": psi(16), "exact": 256 / 27})

    P: list[int] = []
    S = 0.0
    p = 3
    while S < 1:
        if is_prime(p):
            P.append(p)
            S += 1 / p
        p += 2
        if p > 200:
            break
    q = 2
    lo, hi = math.e * (S - 1) / q, math.e * S / q
    rows.append(
        {
            "id": "divisor_cube_interval_shape",
            "ok": S >= 1 and lo < hi and abs(hi - math.e * S / q) < 1e-12,
            "P": P,
            "S": S,
            "lo": lo,
            "hi": hi,
        }
    )

    # Base monotonicity numeric: (y^r-1)/(y^d-1) <= (x^r-1)/(x^d-1) for 1<x<=y.
    mono_ok = True
    for x, y, r, d in ((2, 3, 1, 4), (2, 5, 2, 6), (1.5, 2.0, 0, 3), (2, 2, 3, 5)):
        lhs = (y**r - 1) / (y**d - 1)
        rhs = (x**r - 1) / (x**d - 1)
        if lhs > rhs + 1e-12:
            mono_ok = False
    rows.append({"id": "base_monotonicity_numeric", "ok": mono_ok})

    failed = [r["id"] for r in rows if not r["ok"]]
    return {"mode": "quick", "ok": not failed, "failed": failed, "rows": rows}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true", default=True)
    parser.add_argument("--full", action="store_true")
    args = parser.parse_args()
    if args.full:
        print("full 32800-case mode is not implemented; use --quick", file=sys.stderr)
        return 2
    result = check_quick()
    RECEIPT_DIR.mkdir(parents=True, exist_ok=True)
    receipt = RECEIPT_DIR / "check_signed_finite_period_r4_quick.json"
    receipt.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"ok": result["ok"], "failed": result["failed"], "receipt": str(receipt)}, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
