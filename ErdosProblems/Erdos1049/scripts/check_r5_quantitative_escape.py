#!/usr/bin/env python3
"""Exact finite checks for the R5 ordinary arguments; these are not Lean proofs.
Python 3.10+, standard library only. Run from any directory.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, lcm, isqrt
import json
from pathlib import Path


def determinant(a: list[list[int | F]]) -> F:
    m = [[F(x) for x in row] for row in a]
    ans = F(1)
    for i in range(len(m)):
        pivot = next((j for j in range(i, len(m)) if m[j][i]), None)
        if pivot is None:
            return F(0)
        if pivot != i:
            m[i], m[pivot] = m[pivot], m[i]
            ans = -ans
        x = m[i][i]
        ans *= x
        for j in range(i + 1, len(m)):
            t = m[j][i] / x
            for k in range(i + 1, len(m)):
                m[j][k] -= t * m[i][k]
    return ans


def phi(n: int) -> int:
    return sum(gcd(n, j) == 1 for j in range(1, n + 1))


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def rank_mod(a: list[list[int]], p: int = 1000003) -> int:
    if not a:
        return 0
    m = [[x % p for x in row] for row in a]
    r = 0
    for c in range(len(m[0])):
        j = next((j for j in range(r, len(m)) if m[j][c]), None)
        if j is None:
            continue
        m[r], m[j] = m[j], m[r]
        inv = pow(m[r][c], -1, p)
        m[r] = [x * inv % p for x in m[r]]
        for j in range(r + 1, len(m)):
            if m[j][c]:
                f = m[j][c]
                m[j] = [(x - f*y) % p for x, y in zip(m[j], m[r])]
        r += 1
        if r == len(m):
            break
    return r


def main() -> dict:
    intervals = [(F(1,14),F(1,12)),(F(1,7),F(1,6)),
      (F(3,14),F(1,4)),(F(2,7),F(1,3)),(F(5,14),F(2,5)),
      (F(3,7),F(7,15)),(F(1,2),F(8,15)),(F(4,7),F(3,5)),
      (F(9,14),F(2,3)),(F(5,7),F(11,15)),(F(11,14),F(4,5)),
      (F(6,7),F(13,15)),(F(13,14),F(14,15))]
    j0 = sum(1/u**2 - 1/v**2 for u, v in intervals)
    lower = (266 - F(3)/F(157,50)**2*(225-j0))/F(1091,2)
    assert lower > F(81,200)
    assert 4**200 < 31**81 and 31**2 < 4**5

    # Check omega on every cell of the exact breakpoint arrangement.
    floor = lambda q: q.numerator // q.denominator
    points = sorted({F(k,d) for d in (12,13,14,15) for k in range(d+1)})
    for u,v in zip(points, points[1:]):
        x = (u+v)/2
        value = max(0, floor(14*x)+floor(13*x)-floor(12*x)-floor(15*x),
                    2*floor(14*x)-floor(13*x)-floor(15*x))
        assert value == sum(u <= x < v for u,v in intervals)

    gcases = 0
    for values in combinations(range(1, 11), 4):
        G = [[gcd(a,b) for b in values] for a in values]
        D = divisors(lcm(*values))
        for i,a in enumerate(values):
            for j,b in enumerate(values):
                assert G[i][j] == sum(phi(d) for d in D if a%d==b%d==0)
        assert determinant(G) > 0
        M = lcm(*values)
        for a in values:
            for b in values:
                for k in (1,2,7):
                    assert gcd(a*(1+k*M),b)==gcd(a,b)
        gcases += 1

    assert all(1000003 % d for d in range(2,isqrt(1000003)+1))
    N = 350
    tau = [0]*(N+1)
    for d in range(1,N+1):
        for j in range(d,N+1,d):
            tau[j] += 1
    # Polynomial coefficients of degree <=2, derivative orders 0..2,
    # four mixed dilations. Full rank mod a prime implies full rank over Q
    # for this finite truncation ONLY.
    columns = []
    names = []
    for j in range(3):
        columns.append([int(n==j) for n in range(N+1)])
        names.append(f'z^{j}')
    for m in (1,2,3,6):
        for s in range(3):
            for j in range(3):
                col=[]
                for n in range(N+1):
                    k=n-j
                    col.append(k**s*tau[k//m] if k>0 and k%m==0 else 0)
                columns.append(col)
                names.append(f'z^{j} Theta^{s} L(z^{m})')
    rr = rank_mod([list(row) for row in zip(*columns)])
    assert rr == len(columns)
    # Twist trace identities via tau(p n)=2tau(n)-1_{p|n}tau(n/p).
    for p in (2,3,5,7):
        for n in range(1,N//p+1):
            assert tau[p*n] == 2*tau[n] - (tau[n//p] if n%p==0 else 0)
    for n in range(1,N+1):
        assert ((-1)**n)*tau[n] == (
            4*(tau[n//2] if n%2==0 else 0)-tau[n]
            -2*(tau[n//4] if n%4==0 else 0))

    mu=[0]*(N+1); mu[1]=1
    for n in range(2,N+1):
        mu[n]=-sum(mu[d] for d in divisors(n) if d<n)
    for n in range(1,N+1):
        assert sum(mu[d]*tau[n//d] for d in divisors(n))==1

    # Quantitative escape on exact rational finite data. Both applicability
    # and consequent existence are checked; negative examples remain negative.
    bin_cases=0; successes=0
    for residues in product(range(2),repeat=5):
        vals = [F(a, 8) for a in (1,2,3,5,7)]
        records=[]
        for eps in product((0,1),repeat=5):
            records.append((sum(e*a for e,a in zip(eps,residues))%2,
                            sum(e*v for e,v in zip(eps,vals))))
        mult=max(sum(y==x for y in records) for x in records)
        span=max(g for f,g in records)-min(g for f,g in records)
        for delta in (F(1,16),F(1,8),F(1,2),F(1),F(2),F(3)):
            bins=floor(span/delta)+1
            condition=len(records)>len(set(f for f,g in records))*mult*bins
            found=any(x[0]==y[0] and 0<abs(x[1]-y[1])<delta
                      for x,y in combinations(records,2))
            assert not condition or found
            bin_cases+=1; successes+=condition

    # Exact bin obstruction witness: narrow-family symbolic exponent comparison.
    # log 2 < 1, M <= (m/10+1)^2, so 2^M < exp(5m^2) for m>=1.
    for m in range(1,1001):
        assert (m//10+1)**2 < 5*m*m

    return {
      'status':'all exact assertions passed; no infinite analytic or Lean certification',
      'theta_lower_bound_from_J0_and_pi_gt_157_over_50': str(lower),
      'theta_margin_above_81_over_200': str(lower-F(81,200)),
      'omega_cells_checked':len(points)-1,
      'gcd_gram_matrices_checked':gcases,
      'mixed_derivative_Taylor_columns':len(columns),
      'Taylor_coefficients_through':N,
      'Taylor_rank_mod_1000003':rr,
      'mobius_inversion_coefficients_checked':N,
      'finite_binning_cases':bin_cases,
      'applicable_binning_cases':successes,
      'G_1_2_3_determinant':str(determinant([[gcd(a,b) for b in (1,2,3)] for a in (1,2,3)]))
    }

if __name__ == '__main__':
    result=main()
    text=json.dumps(result,indent=2)
    print(text)
    Path(__file__).with_name('check_results.json').write_text(text+'\n',encoding='utf-8')
