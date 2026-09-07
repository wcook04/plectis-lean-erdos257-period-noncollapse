#!/usr/bin/env python3
"""Algebra of the interval-optimal continued-fraction denominator extraction.

Does not rerun the 80000-bit Erdős #68 enclosure. The live lead remains
q >= 2^39990 > 10^12038 from the last common convergent.

Usage:
  ./repo-python Erdos68/scripts/check_interval_optimal_cf_extraction.py --quick
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import gcd


def image(pj: int, qj: int, pjm1: int, qjm1: int, u: int, v: int) -> tuple[int, int]:
    P = pj * u + pjm1 * v
    Q = qj * u + qjm1 * v
    g = gcd(P, Q)
    return P // g, Q // g


def run_quick() -> None:
    # Common prefix [0;1,2]: last convergent 2/3, predecessor 1/1.
    pj, qj, pjm1, qjm1 = 2, 3, 1, 1
    alpha = Fraction(99, 2)  # 49.5
    beta = Fraction(100, 1)
    assert 49 < alpha < 50 < beta < 237
    k = int(alpha) + 1
    assert k == 50
    Pstar, Qstar = image(pj, qj, pjm1, qjm1, k, 1)
    assert Qstar == 50 * qj + qjm1
    a_p, a_q = image(pj, qj, pjm1, qjm1, 99, 2)
    b_p, b_q = image(pj, qj, pjm1, qjm1, 100, 1)
    left = Fraction(a_p, a_q)
    right = Fraction(b_p, b_q)
    lo, hi = (left, right) if left < right else (right, left)
    mid = Fraction(Pstar, Qstar)
    assert lo < mid < hi
    # det = p_j q_{j-1} - p_{j-1} q_j = -1, so the complete-quotient map decreases.

    # v >= 2 forces u >= 99, hence a strictly larger denominator.
    Q_comp = 99 * qj + 2 * qjm1
    assert Q_comp > Qstar
    # v = 1 forces u >= 50, hence denominator >= Qstar.
    assert 50 * qj + qjm1 == Qstar

    # Unimodularity of the CF matrix: no cancellation at the attaining tail 50.
    assert abs(pj * qjm1 - pjm1 * qj) == 1
    assert gcd(Pstar, Qstar) == 1

    # Closed-endpoint counterexample: after prefix [0;1,2], the closed
    # complete-quotient interval [49, 51] maps to [103/154, 99/148].
    # The open-interval rule k = floor(49)+1 = 50 is not minimal on the closed
    # interval, because the included endpoint 99/148 has smaller denominator.
    f = lambda t: (2 * t + 1) / (3 * t + 1)
    assert f(Fraction(49)) == Fraction(99, 148)
    assert f(Fraction(51)) == Fraction(103, 154)
    assert f(Fraction(50)) == Fraction(101, 151)
    lo, hi = Fraction(103, 154), Fraction(99, 148)
    best = None
    for q in range(1, 152):
        a = (lo.numerator * q + lo.denominator - 1) // lo.denominator
        if Fraction(a, q) <= hi:
            best = (a, q)
            break
    assert best == (99, 148)
    # Closed rule uses k = ceil(alpha) = 49, attained at the endpoint.

    # Separate power comparisons: do not chain 2^39996 > 10^12040.
    # 39996 log10(2) < 12040, so 2^39996 < 10^12040.
    assert pow(2, 39996) < pow(10, 12040)
    print("check_interval_optimal_cf_extraction: PASS")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.parse_args()
    run_quick()


if __name__ == "__main__":
    main()
