#!/usr/bin/env python3
"""Exact finite checks of the new dyadic-shell estimate and countermodels.

Uses only Python's standard library. This is finite evidence, not a proof of
any infinite-support theorem. Output has no floating-point mathematical claims.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from math import gcd
from pathlib import Path
import json
import hashlib


def atom_numerators(p: int, q: int, L: int, d: int) -> tuple[list[int], int]:
    """One exact orbit; B=p/q. All atoms have denominator p**d-q**d."""
    den = p ** d - q ** d
    out = [0]
    for m in range(1, d // gcd(L, d) + 1):
        r = L * m % d
        out.append(out[-1] + p ** r * q ** (d - r))
    return out, den


def avg(prefix: list[int], den: int, T: int) -> Q:
    period = len(prefix) - 1
    cycles, rem = divmod(T, period)
    return Q(cycles * prefix[-1] + prefix[rem], T * den)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    bases = [(2, 1), (3, 2), (5, 4), (17, 16), (257, 256)]
    ls = range(1, 9 if args.quick else 17)
    ds = range(1, 33 if args.quick else 97)
    rs = range(4)
    ms = range(1, 6)
    shell_count = 0
    regime_count = 0
    minimum_slack: Q | None = None
    min_at: list[int] | None = None
    for p, q in bases:
        B = Q(p, q)
        for L in ls:
            for d in ds:
                prefix, den = atom_numerators(p, q, L, d)
                av = [avg(prefix, den, 2 ** j) for j in range(10)]
                for j, value in enumerate(av):
                    T = 2 ** j
                    mu = 1 / (d * (B - 1))
                    if d <= L * T:
                        bound = mu + 1 / (T * (B - 1))
                    elif d > 2 * L * T:
                        bound = mu
                    else:
                        bound = 2 * L * mu
                    assert value <= bound, ('regime', p, q, L, d, j, value, bound)
                    regime_count += 1
                for R in rs:
                    for M in ms:
                        lhs = sum(av[R:R + M], Q(0)) / M
                        rhs = (1 + Q(4 * L, M)) / (d * (B - 1))
                        slack = rhs - lhs
                        assert slack >= 0, ('shell', p, q, L, d, R, M, lhs, rhs)
                        shell_count += 1
                        if minimum_slack is None or slack < minimum_slack:
                            minimum_slack, min_at = slack, [p, q, L, d, R, M]
    # The coefficient-lattice boundary: exact telescoping on squares.
    telescope_count = 0
    for b in range(2, 9):
        total = Q(0)
        for j in range(1, 21):
            a, nxt = j * j, (j + 1) ** 2
            lam = (b ** a - 1) * (Q(1, b ** a) - Q(1, b ** nxt))
            assert 0 < lam < 1
            total += lam / (b ** a - 1)
            assert total == Q(1, b) - Q(1, b ** nxt)
            telescope_count += 1
    # Logical non-synchronisation model, not a Mersenne support.
    nonsync_count = 0
    for n in range(1, 1001):
        f = Q(1, n + 1) if n % 2 == 0 else Q(1)
        g = Q(1) if n % 2 == 0 else Q(1, n + 1)
        assert f + g == 1 + Q(1, n + 1) > 1
        nonsync_count += 1
    # Check the exact global upper bound used in the prime-core barrier.
    partial = Q(0)
    prime_bound_count = 0
    for a in range(2, 301):
        partial += Q(1, 2 ** a - 1)
        outer_bound = Q(4, 3) * Q(1, 2 ** a)
        assert partial + outer_bound < Q(2, 3) if a > 2 else partial + outer_bound <= Q(2, 3)
        prime_bound_count += 1
    result = {
        'status': 'pass',
        'arithmetic': 'fractions.Fraction and exact integers only',
        'dyadic_shell_cases': shell_count,
        'near_far_transition_cases': regime_count,
        'bases': [f'{p}/{q}' for p, q in bases],
        'ranges': {'L': [min(ls), max(ls)], 'd': [min(ds), max(ds)],
                   'R': [min(rs), max(rs)], 'M': [min(ms), max(ms)]},
        'minimum_shell_slack': str(minimum_slack),
        'minimum_shell_slack_at_p_q_L_d_R_M': min_at,
        'telescoping_coefficient_cases': telescope_count,
        'abstract_nonsynchronisation_cases': nonsync_count,
        'partial_sum_upper_bound_cases': prime_bound_count,
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'limitations': [
            'No infinite prime blocks or infinite supports were enumerated.',
            'No Lean compiler or Comparator build was run.',
            'The general inequalities and hybrid theorem depend on the ordinary proofs.'
        ],
    }
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(text)


if __name__ == '__main__':
    main()
