#!/usr/bin/env python3
"""Exact finite tests for the round-5 ordinary construction.

These tests do not prove any infinite theorem, do not use prime data, and do
not substitute for the unavailable Lean build. Only integer/Fraction arithmetic
is used for the construction identities and greedy remainders.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import json
from random import Random
from typing import Sequence


def arc_deficiency(values: Sequence[int], modulus: int, classes: int,
                   arc_steps: int) -> int:
    """Reference implementation; the arc contains arc_steps+1 residues."""
    if not 1 <= arc_steps < modulus or classes < 1:
        raise ValueError("Require 1 <= arc_steps < modulus and classes >= 1")
    groups: dict[int, list[int]] = defaultdict(list)
    for i, value in enumerate(values):
        groups[i % classes].append(value % modulus)
    out = 0
    for points in groups.values():
        best = max(sum((x - start) % modulus <= arc_steps for x in points)
                   for start in range(modulus))
        out += len(points) - best
    return out


def run(seed: int, cases: int) -> dict[str, object]:
    rng = Random(seed)
    pairs = buffers = telescope = greedy = coupling = arcs = 0
    for _ in range(cases):
        size = rng.randrange(2, 18)
        n = [rng.randrange(2, 12)]
        M = [2]
        D = [rng.randrange(1, 6)]
        for j in range(1, size):
            n.append(n[-1] + rng.randrange(4, 10))
            M.append(M[-1] * rng.randrange(1, 5))
            D.append((1 << (n[-1] - n[-2])) - 1)
        w = [Fraction(m, 1 << (index + 2)) for m, index in zip(M, n)]
        # Constant multiplier after the final site gives exact remaining
        # capacity w[-1], by the same telescope. This is a finite test fixture.
        capacity = [Fraction(0)] * (size + 1)
        capacity[size] = w[-1]
        for j in reversed(range(size)):
            capacity[j] = D[j] * w[j] + capacity[j + 1]
            assert w[j] <= capacity[j + 1]
        y = Fraction(rng.randrange(0, 1001), 1000) * capacity[0]
        rem = y
        digits: list[int] = []
        for j in range(size):
            d = min(D[j], rem // w[j])
            assert isinstance(d, int) and 0 <= d <= D[j]
            rem -= d * w[j]
            assert 0 <= rem <= capacity[j + 1]
            digits.append(d)
            greedy += 1
        assert sum((d * weight for d, weight in zip(digits, w)), Fraction(0)) == y - rem
        C = 0
        actual: dict[int, int] = {}
        weighted_pairs = Fraction(0)
        buffers_value = Fraction(0)
        for j in range(size):
            c = (-C) % M[j]
            assert 0 <= c < M[j] and (C + c) % M[j] == 0
            if j:
                assert c % M[j - 1] == 0
            d = digits[j]
            left, right = M[j] * d, M[j] * (D[j] - d)
            assert left + right == M[j] * D[j]
            weighted = Fraction(left, 1 << (n[j] + 1)) + Fraction(right, 1 << (n[j] + 2))
            assert weighted == M[j] * (D[j] + d) * Fraction(1, 1 << (n[j] + 2))
            assert not any(i in actual for i in (n[j] - 1, n[j], n[j] + 1))
            actual.update({n[j] - 1: c, n[j]: left, n[j] + 1: right})
            C += c + left + right
            assert C % M[j] == 0
            pairs += 1
            buffers += 1
            buffers_value += Fraction(c, 1 << n[j])
            weighted_pairs += weighted
            if j:
                exact = M[j] * (Fraction(1, 1 << (n[j-1]+2)) - Fraction(1, 1 << (n[j]+2)))
                assert D[j] * w[j] == exact
                assert D[j] * w[j] >= M[j-1] * (Fraction(1, 1 << (n[j-1]+2)) - Fraction(1, 1 << (n[j]+2)))
                telescope += 1
        actual_sum = sum((Fraction(e, 1 << (i+1)) for i, e in actual.items()), Fraction(0))
        assert actual_sum == buffers_value + weighted_pairs
        assert weighted_pairs == sum((D[j]*w[j] for j in range(size)), Fraction(0)) + y - rem
        for j in range(size):
            # The congruence starts after the buffer, as in the proof.
            for index in range(n[j], n[-1] + 3):
                assert actual.get(index, 0) % M[j] == 0
                assert sum(e for i, e in actual.items() if i < index) % M[j] == 0

        X = rng.randrange(4, 45)
        length = rng.randrange(1, X + 1)
        a = [rng.randrange(1, 15) for _ in range(2*X + length)]
        b = a.copy()
        changed = set(rng.sample(range(X, 2*X+length-1), rng.randrange(0, min(X, 8)+1)))
        for i in changed:
            b[i] += rng.randrange(1, 8)
        aa = [tuple(a[i:i+length]) for i in range(X, 2*X)]
        bb = [tuple(b[i:i+length]) for i in range(X, 2*X)]
        affected = sum(u != v for u, v in zip(aa, bb))
        assert affected <= length * len(changed)
        ca, cb = Counter(aa), Counter(bb)
        l1 = sum(abs(ca[k] - cb[k]) for k in ca.keys() | cb.keys())
        assert l1 <= 2 * affected
        coupling += 1

        Q = 1 << rng.randrange(2, 6)
        r = [rng.randrange(Q) for _ in range(X)]
        s = r.copy()
        indices = rng.sample(range(X), rng.randrange(X+1))
        for i in indices:
            s[i] = rng.randrange(Q)
        t, K = rng.randrange(1, X+2), rng.randrange(1, Q)
        assert abs(arc_deficiency(r, Q, t, K) - arc_deficiency(s, Q, t, K)) <= sum(u != v for u, v in zip(r, s))
        arcs += 1
    return {"seed": seed, "cases": cases, "pair_identities": pairs,
            "buffer_invariants": buffers, "capacity_telescopes": telescope,
            "greedy_steps": greedy, "block_coupling_tests": coupling,
            "arc_lipschitz_tests": arcs, "arithmetic": "integers and exact fractions",
            "status": "passed", "infinite_theorem_proved_by_tests": False,
            "lean_build_performed": False, "prime_data_used": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=25105)
    parser.add_argument('--cases', type=int, default=500)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.cases < 1:
        parser.error('--cases must be positive')
    result = json.dumps(run(args.seed, args.cases), indent=2) + '\n'
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(result)
    print(result, end='')

if __name__ == '__main__':
    main()
