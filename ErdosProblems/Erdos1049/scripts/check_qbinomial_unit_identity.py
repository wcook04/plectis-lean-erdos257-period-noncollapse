#!/usr/bin/env python3
"""Integer check of the finite q-binomial algebra used by Type B r4 (2.3).

Stdlib only.  Corroborates QBinomialUnitIdentity.lean and the D_s arithmetic
in PrimitiveTwoAdicMinor.lean.  Does not construct source sums A(p), B(p),
and does not decide F(3/2).
"""

from __future__ import annotations


def q_pochhammer(q: int, z: int, n: int) -> int:
    acc = 1
    for i in range(n):
        acc *= 1 - z * q**i
    return acc


def gauss_binom(q: int, n: int, k: int) -> int:
    if k < 0 or n < 0:
        raise ValueError("indices must be nonnegative")
    table = [0] * (k + 1)
    table[0] = 1
    for m in range(1, n + 1):
        nxt = [0] * (k + 1)
        nxt[0] = 1
        for r in range(1, k + 1):
            if r > m:
                nxt[r] = 0
            else:
                nxt[r] = table[r] + q ** (m - r) * table[r - 1]
        table = nxt
    return table[k]


def q_binomial_sum(q: int, z: int, n: int) -> int:
    acc = 0
    for k in range(n + 1):
        acc += gauss_binom(q, n, k) * ((-1) ** k) * (q ** (k * (k - 1) // 2)) * (z**k)
    return acc


def source_inner_t(q: int, a: int, d: int, v: int, alpha: int) -> int:
    acc = 0
    for j in range(v):
        acc += (
            ((-1) ** j)
            * (q ** (j * (j - 1) // 2 + alpha * j))
            * gauss_binom(q, v - 1, j)
            * gauss_binom(q, a + d + j - 1, a - 1)
        )
    return acc


def source_inner_t_rhs(q: int, a: int, d: int, v: int, alpha: int) -> int:
    acc = 0
    for h in range(a):
        acc += (
            ((-1) ** h)
            * (q ** (h * (d + 1) + h * (h - 1) // 2))
            * gauss_binom(q, a - 1, h)
            * q_pochhammer(q, q ** (alpha + h), v - 1)
        )
    return acc


def three_adic_d(n: int, s: int) -> int:
    return (2 * n - s) * (n + 1 - s)


def main() -> int:
    for q, z, n in ((2, 3, k) for k in range(9)):
        left = q_pochhammer(q, z, n)
        right = q_binomial_sum(q, z, n)
        if left != right:
            raise SystemExit(f"q-binomial failed at q={q} z={z} n={n}: {left} vs {right}")
        if n >= 1 and gauss_binom(q, n, n) != 1:
            raise SystemExit(f"gaussBinom self failed at n={n}")
    for n in range(12):
        for k in range(n + 1):
            left = gauss_binom(2, n, k) * q_pochhammer(2, 2, k)
            right = q_pochhammer(2, 2 ** (n - k + 1), k)
            if left != right:
                raise SystemExit(f"gauss * (q;q)_k failed at n={n} k={k}")
    for a, d, v, alpha in ((1, 0, 1, 1), (2, 1, 2, 1), (3, 2, 3, 2), (4, 1, 3, 1)):
        left = q_pochhammer(2, 2, a - 1) * source_inner_t(2, a, d, v, alpha)
        right = source_inner_t_rhs(2, a, d, v, alpha)
        if left != right:
            raise SystemExit(f"(2.3) failed at {(a, d, v, alpha)}: {left} vs {right}")
    for n in range(2, 12):
        if three_adic_d(n, 2) != 2 * (n - 1) ** 2:
            raise SystemExit(f"D_2 failed at n={n}")
        if not (three_adic_d(n, 2) < three_adic_d(n, 1) < three_adic_d(n, 0)):
            raise SystemExit(f"D_s not strictly decreasing at n={n}")
    print("ok  q-binomial, (2.3) samples, D_s arithmetic")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
