#!/usr/bin/env python3
"""Exact small checks for the divisor-coordinate channel basis (Type B r4).

Does not rerun the 300000 carry census or the 80000-bit enclosure.

Usage:
  ./repo-python Erdos68/scripts/check_divisor_channel_basis.py --quick
"""

from __future__ import annotations

import argparse
from math import factorial, lcm


Vector = dict[int, int]


def clean(v: Vector) -> Vector:
    return {n: c for n, c in v.items() if c}


def add(x: Vector, y: Vector, scale: int = 1) -> Vector:
    z = x.copy()
    for n, c in y.items():
        z[n] = z.get(n, 0) + scale * c
    return clean(z)


def weight(d: int, n: int) -> int:
    q, r = divmod(factorial(n), factorial(d) ** (n // d))
    assert r == 0
    return q


def moment(v: Vector) -> int:
    return sum(c * factorial(n) for n, c in v.items())


def channel(d: int, v: Vector) -> int:
    return sum(c * weight(d, n) for n, c in v.items())


def make_u(bound: int) -> dict[int, Vector]:
    us: dict[int, Vector] = {}
    for n in range(2, bound + 1):
        u = {n - 1: n, n: -1}
        for d in range(2, n):
            if n % d == 0:
                u = add(u, us[d], -weight(d, n))
        assert moment(u) == 0
        for d in range(2, bound + 2):
            assert channel(d, u) == (factorial(n) - 1 if d == n else 0)
        assert n % 2 == 0 or 1 not in u
        us[n] = u
    return us


def run_quick() -> None:
    us = make_u(20)
    assert us[9] == {8: 9, 9: -1, 2: -5040, 3: 1680}
    for n in range(2, 41):
        assert (factorial(n) - 2 * weight(2, n)) % 12 == 0
    sharp = {2: {2: -6, 4: 1}, 3: {2: -6, 3: -8, 4: 5}}
    for D, v in sharp.items():
        L = lcm(*(factorial(d) - 1 for d in range(2, D + 1)))
        assert all(channel(d, v) == 0 for d in range(2, D + 1))
        assert moment(v) == 12 * L
        assert 1 not in v
    # Support n>=2 plus M=L_D is even-versus-odd for every D>=2.
    for D in range(2, 13):
        L = lcm(*(factorial(d) - 1 for d in range(2, D + 1)))
        assert L % 2 == 1
    print("check_divisor_channel_basis: PASS")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.parse_args()
    run_quick()


if __name__ == "__main__":
    main()
