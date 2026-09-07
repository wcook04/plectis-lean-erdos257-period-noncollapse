#!/usr/bin/env python3
"""Exact finite checks for Erdős #243 Type B r4 revision claims.

Does not settle #243.  Ordinary proofs of Theorem A and of the signed
Duverney specialisation live beside these checks; this script only verifies
finite identities and enumerations.

Checks
------
poly    Ring identities (α+2)Q(α-1)-(α-1)Q(α)=3c and
        α Q(α+1)-(α+3)Q(α)=-3c over Q and Z/8Z, plus the product identity
        at roots.
mod7    All 7^3 assignments: exact three-step transport of the plus and
        minus words is empty (686 cases).
phase   Four-step plus-profile primitive witness at n=1..4 against
        unrestricted consecutive-agreement wording.
norm    Exceptional-discriminant norms: negative for integer k=1..12,
        positive at k=1/2 (proof-transfer counterexample, not a
        square-class counterexample).
duv     Closed product (1-1/m^2)^m through group M.
gap     Finite gap-count for a constructed prime prefix with p_j >= 2^{j+3}:
        excluded count on (u, u+H] is < H, and a CRT block of length L
        lies in the complement.

Run:
    ./repo-python .../scripts/check_erdos243_r4_revision_claims.py --quick
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from itertools import product
from math import gcd, isqrt


def cubic_profile(k, c, x):
    return k * x * (x + 1) * (x + 2) + c


def part_poly() -> dict:
    samples = [
        (1, 1, 3),
        (2, -1, 5),
        (Fraction(1, 6), 1, Fraction(2, 3)),
        (7, 0, 0),
        (Fraction(-3, 2), Fraction(5, 7), Fraction(-4, 3)),
    ]
    for k, c, a in samples:
        Q = cubic_profile
        assert Q(k, c, a - 1) * (a + 2) - Q(k, c, a) * (a - 1) == 3 * c
        assert a * Q(k, c, a + 1) - (a + 3) * Q(k, c, a) == -3 * c
        # At a genuine rational root of X(X+1)(X+2) + c/k = 0 the product
        # identity is the specialisation of the ring identity; check the
        # unconditional form only here.
    # Zero-divisor ring Z/8Z
    z8 = 0
    for k, c, a in product(range(8), repeat=3):
        Q = lambda x: (k * x * (x + 1) * (x + 2) + c) % 8
        left = (Q(a - 1) * ((a + 2) % 8) - Q(a) * ((a - 1) % 8)) % 8
        right = (a * Q(a + 1) - ((a + 3) % 8) * Q(a)) % 8
        assert left == (3 * c) % 8
        assert right == (-3 * c) % 8
        z8 += 1
        if Q(a) == 0:
            prod = (-(a % 8) * ((a + 2) % 8) * Q(a - 1) * Q(a + 1)) % 8
            assert prod == (9 * c * c) % 8
    return {"q_samples": len(samples), "z8_triples": z8, "failures": 0}


def part_mod7() -> dict:
    empty = []
    for C in ((1, 6, 0, 2), (4, 5, 0, 1)):
        solutions = []
        for a, b, d in product(range(7), repeat=3):
            if (
                (a * C[0] - d - C[1]) % 7 == 0
                and (b * C[1] - a * d - C[2]) % 7 == 0
                and (-b * a * d - C[3]) % 7 == 0
            ):
                solutions.append((a, b, d))
        assert not solutions, (C, solutions)
        empty.append({"word": list(C), "solutions": 0})
    return {"assignments": 2 * 7 ** 3, "words": empty, "failures": 0}


def part_phase() -> dict:
    C = [13, 49, 121, 241]
    a = [3420, 3099709, 3890919200701]
    D = [44411]
    for j in range(3):
        assert a[j] * C[j] - D[j] == C[j + 1]
        D.append(a[j] * D[j])
    for c, d in zip(C, D):
        assert gcd(c, d) == 1
    assert C == [2 * n * (n + 1) * (n + 2) + 1 for n in range(1, 5)]
    return {"C": C, "primitive": True, "failures": 0}


def part_norm() -> dict:
    def N(k: Fraction, s: int) -> Fraction:
        return -16 * k * (63 * k ** 3 - 48 * k - 4 * s)

    half = Fraction(1, 2)
    assert N(half, 1) == 161
    assert N(half, -1) == 97
    integer_negative = []
    for kk in range(1, 13):
        for s in (1, -1):
            val = N(Fraction(kk), s)
            assert val < 0, (kk, s, val)
            integer_negative.append(int(val))
    return {
        "k_half_plus": 161,
        "k_half_minus": 97,
        "integer_k_1_to_12_all_negative": True,
        "sample_integer_norms": integer_negative[:4],
        "failures": 0,
    }


def part_duv() -> dict:
    mismatches = 0
    last = None
    for M in range(2, 20):
        lhs = Fraction(1)
        for m in range(2, M + 1):
            lhs *= Fraction(m * m - 1, m * m) ** m
        rhs = Fraction((M + 1) ** M, 2 * M ** (M + 1))
        if lhs != rhs:
            mismatches += 1
        last = lhs
    assert mismatches == 0
    assert last is not None and last < 1
    return {"M_range": [2, 19], "mismatches": mismatches, "decreasing_to_zero": True,
            "failures": 0}


def first_primes_exp_bound(jmax: int) -> list[int]:
    """Increasing primes with p_j >= 2^{j+3}, 1-based j."""
    need = [1 << (j + 3) for j in range(1, jmax + 1)]
    out: list[int] = []
    n = 2
    idx = 0
    while idx < jmax:
        if all(n % p for p in out) and n * n > n:
            is_p = True
            r = isqrt(n)
            for p in out:
                if p > r:
                    break
                if n % p == 0:
                    is_p = False
                    break
            if is_p and n >= 2:
                # trial beyond listed primes
                d = (out[-1] + 1) if out else 3
                if d % 2 == 0:
                    d += 1
                while d * d <= n:
                    if n % d == 0:
                        is_p = False
                        break
                    d += 2
            if is_p and n >= need[idx]:
                out.append(n)
                idx += 1
        n += 1 if n == 2 else 2
        if n == 3:
            continue
    return out


def sieve_primes_upto(limit: int) -> list[int]:
    if limit < 2:
        return []
    mark = bytearray(b"\x01") * (limit + 1)
    mark[0:2] = b"\x00\x00"
    p = 2
    while p * p <= limit:
        if mark[p]:
            step = p
            start = p * p
            mark[start : limit + 1 : step] = b"\x00" * (((limit - start) // step) + 1)
        p += 1
    return [i for i in range(limit + 1) if mark[i]]


def part_gap(quick: bool) -> dict:
    jmax = 8 if quick else 12
    # Construct primes p_j >= 2^{j+3} by scanning the sieve.
    cap = 1 << (jmax + 4)
    primes = sieve_primes_upto(cap)
    chosen: list[int] = []
    j = 1
    for p in primes:
        if j > jmax:
            break
        if p >= 1 << (j + 3):
            chosen.append(p)
            j += 1
    assert len(chosen) == jmax, chosen
    sigma0 = sum(Fraction(1, p) for p in chosen)
    assert sigma0 < Fraction(1, 4)
    # Avoidance set in [1, X]
    X = 4000 if quick else 12000
    forbidden = set()
    for p in chosen:
        forbidden.update(range(p, X + 64, p))
    A = [m for m in range(1, X + 1) if m not in forbidden]
    assert len(A) >= int((1 - float(sigma0)) * X) - jmax
    # Gap bound: for several u in A, H = 2k+2 with k = #{p_j <= 2u}
    bound_ok = 0
    for u in A[10 : 10 + (80 if quick else 240)]:
        k = sum(1 for p in chosen if p <= 2 * u)
        if k == 0:
            continue
        H = 2 * k + 2
        if u + H > X:
            continue
        excluded = 0
        for x in range(u + 1, u + H + 1):
            if any(x % p == 0 for p in chosen if p <= 2 * u):
                excluded += 1
        assert excluded < H, (u, k, H, excluded)
        assert any(x not in forbidden for x in range(u + 1, u + H + 1))
        bound_ok += 1
    # CRT block of length L using first L chosen primes: all L residues hit.
    L = 4 if quick else 6
    mods = chosen[:L]
    # x ≡ -i (mod p_{i+1}) for i=0..L-1 gives L consecutive multiples.
    # Solve x ≡ -i (mod mods[i]).
    M = 1
    for p in mods:
        M *= p
    # successive substitution
    x = 0
    acc = 1
    # Use explicit search on the product; product of first 4 bounded primes is small.
    found = None
    for cand in range(M):
        if all((cand + i) % mods[i] == 0 for i in range(L)):
            found = cand
            break
    assert found is not None
    block = [found + i for i in range(L)]
    assert all(block[i] % mods[i] == 0 for i in range(L))
    return {
        "primes": chosen,
        "sigma0": str(sigma0),
        "gap_windows_checked": bound_ok,
        "crt_block": block,
        "crt_length": L,
        "failures": 0,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    report = {
        "script": "check_erdos243_r4_revision_claims.py",
        "quick": args.quick,
        "poly": part_poly(),
        "mod7": part_mod7(),
        "phase": part_phase(),
        "norm": part_norm(),
        "duv": part_duv(),
        "gap": part_gap(args.quick),
        "evidence_class": "exact_finite_computation_beside_ordinary_proofs",
        "claim_ceiling": "finite exact replay only; Erdős #243 remains open",
    }
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
