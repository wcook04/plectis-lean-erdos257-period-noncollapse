#!/usr/bin/env python3
"""Exact finite checks supporting r5; no network or third-party packages.

These checks do not prove the infinite CRT theorem or the analytic transfer.
Run: python3 checks/check_r5.py [--output checks/receipt.json]
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
from math import gcd, lcm, prod
from pathlib import Path
import json


def check_cycle(steps: int = 12) -> dict:
    L, U, partial = 1, 1, Fraction(0)
    rows = []
    previous_a = 0
    for n in range(steps):
        b = 1 if n % 2 == 0 else 3
        if n % 2 == 0:
            assert U == 1 and L % 2 == 1
            a = L + 2
        else:
            assert U == 2 and L % 4 == 3
            a = (3 * L + 1) // 2
        assert a > previous_a and gcd(a, L) == 1
        Unext = a * U - b * L
        Lnext = lcm(a, L)
        V = b * L - (a - 1) * U
        assert Unext == (2 if n % 2 == 0 else 1)
        assert V == (-1 if n % 2 == 0 else 1)
        partial += Fraction(b, a)
        assert partial + Fraction(Unext, Lnext) == 1
        rows.append({"n": n, "b": b, "a": str(a) if n < 5 else None,
                     "a_bits": a.bit_length(), "U": U, "V": V, "rho": 1})
        L, U, previous_a = Lnext, Unext, a
    return {"steps": steps, "all_exact": True, "initial_rows": rows[:6],
            "final_L_bits": L.bit_length()}


def check_unit_overlap(steps: int = 12) -> dict:
    k, partial, previous = 1, Fraction(0), 0
    initial = []
    for n in range(steps):
        L, a, knext = 2 * k, 2 * (k + 1), k * (k + 1)
        assert a > previous and gcd(L, a) == 2
        assert lcm(L, a) == 2 * knext
        assert a - L == 2 and L - (a - 1) == -1
        partial += Fraction(1, a)
        assert partial + Fraction(1, 2 * knext) == Fraction(1, 2)
        if n < 5:
            initial.append(a)
        k, previous = knext, a
    return {"steps": steps, "initial_denominators": initial, "all_exact": True}


def check_old_multiplier(steps: int = 8) -> dict:
    L, U, partial = 1, 2, Fraction(0)
    for n in range(steps):
        a, b = (3, 3) if n == 0 else (L + 1, 3)
        rho = gcd(L, a)
        assert rho == 1
        Unext, Lnext = a * U - b * L, lcm(L, a)
        assert Unext == 3 and Unext % 3 == 0
        partial += Fraction(b, a)
        assert partial + Fraction(Unext, Lnext) == 2
        L, U = Lnext, Unext
    return {"steps": steps, "old_multiplier": 3, "later_numerators": 3,
            "all_exact": True}


def check_fences() -> dict:
    # For each CRT cover, enumerate many one-step states and all integral
    # b in a bounded interval. A crossing satisfying all hypotheses is forbidden.
    families = {1: [2], 2: [3, 5], 3: [5, 7, 11], 4: [5, 7, 11, 13]}
    tested = viable = 0
    certificates = []
    for B, ms in families.items():
        P = prod(ms)
        z = next(x for x in range(B + 1, B + P + 1)
                 if all((x + i) % m == 0 for i, m in enumerate(ms)))
        assert B < z and all(m > B for m in ms)
        # Only the B potentially crossing source heights need enumeration;
        # the ordinary proof explains why smaller sources cannot cross.
        for u in range(z, z + B):
            for a in range(2, 61):
                rho = gcd(P, a)
                for b in range(-3, 61):
                    tested += 1
                    numerator = a * u - b * P
                    if numerator <= 0 or numerator % rho:
                        continue
                    v = numerator // rho
                    V = b * P - (a - 1) * u
                    if V < -B:
                        continue
                    viable += 1
                    assert rho * v == u - V
                    assert v < z + B
        certificates.append({"B": B, "moduli": ms, "period": P,
                             "z": z, "excluded_threshold": z + B})
    return {"candidate_transitions": tested, "admissible_transitions": viable,
            "counterexamples": 0, "certificates": certificates}


def check_freshness_threshold() -> dict:
    # Strict record freshness holds under V >= -U. Any uniform relaxation
    # by a factor >1 permits overlap, witnessed by this exact family.
    for m in range(2, 102):
        U, L, a, b = 2 * m, 4 * m - 2, 4, 1
        rho = gcd(L, a)
        assert rho == 2
        V = b * L - (a - 1) * U
        assert V == -2 * m - 2
        assert (a * U - b * L) // rho == U + 1
    return {"instances": 100, "exact_overlap_records": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = {
        "status": "PASS", "arithmetic": "exact integers and fractions",
        "scope": "finite checks only; not Lean or infinite-theorem verification",
        "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "coefficient_cycle": check_cycle(),
        "unit_overlap_example": check_unit_overlap(),
        "old_multiplier_example": check_old_multiplier(),
        "divisor_fences": check_fences(),
        "freshness_threshold": check_freshness_threshold(),
    }
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text)

if __name__ == "__main__":
    main()
