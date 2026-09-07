#!/usr/bin/env python3
"""Exact finite checks for the round-5 memorandum. Standard library only.

All arithmetic is integer/Fraction arithmetic. These tests check finite algebra
and actual kernel entries, not an infinite irrationality assertion.
"""
from __future__ import annotations
import argparse
import itertools
import json
from bisect import bisect_left
from fractions import Fraction as Q
from pathlib import Path


def rank(a: list[list[Q]]) -> int:
    if not a:
        return 0
    a = [list(map(Q, row)) for row in a]
    m, n, r = len(a), len(a[0]), 0
    for j in range(n):
        pivot = next((i for i in range(r, m) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        z = a[r][j]
        a[r] = [v/z for v in a[r]]
        for i in range(r + 1, m):
            z = a[i][j]
            if z:
                a[i] = [v-z*w for v, w in zip(a[i], a[r])]
        r += 1
        if r == m:
            break
    return r


def height(x: int, primes: tuple[int, ...] = (2, 3, 5)) -> int:
    if x < 1:
        raise ValueError('positive cutoff required')
    h = 1
    for p in primes:
        z = 1
        while z*p <= x:
            z *= p
        h *= z
    return h


def kernel(i: int, j: int, k: int = 0) -> Q:
    return Q(1, height(2**i * 3**j * 5**k))


def power_phases(p: int, r: int, n: int) -> list[Q]:
    """r**{i log_r p}, represented as an exact rational; no logarithms."""
    power = rp = 1
    values = []
    for _ in range(n):
        while rp*r <= power:
            rp *= r
        values.append(Q(power, rp))
        power *= p
    return values


def leading_rank(n: int) -> int:
    if n == 0:
        return 0
    xs = sorted(power_phases(2, 5, n))
    ys = power_phases(3, 5, n)
    cuts = {bisect_left(xs, Q(5)/y) for y in ys}
    return len(cuts) - int(0 in cuts and n in cuts)


def cut_matrix(m: int, cuts: list[int], c: Q) -> list[list[Q]]:
    return [[Q(1) if i < k else c for k in cuts] for i in range(m)]


def gap(points: list[Q]) -> Q:
    z = sorted(set(points))
    return max([b-a for a,b in zip(z,z[1:])] + [1+z[0]-z[-1]])


def circle_dist(x: Q) -> Q:
    x %= 1
    return min(x, 1-x)


def run() -> dict[str, object]:
    counts: dict[str, int] = {}
    total = 0
    for m in range(1, 7):
        for mask in range(1, 1 << (m+1)):
            cuts = [k for k in range(m+1) if mask >> k & 1]
            expected = len(cuts) - int(0 in cuts and m in cuts)
            for c in (Q(1,5), Q(2,3), Q(-2), Q(2)):
                assert rank(cut_matrix(m,cuts,c)) == expected
                total += 1
    counts['finite_cut_rank_cases'] = total
    for n in range(1,25):
        for k in range(3):
            assert rank([[kernel(i,j,k) for j in range(n)] for i in range(n)]) == leading_rank(n)
    counts['actual_kernel_gaussian_checks'] = 72
    for j in range(4):
        assert kernel(3,j) == kernel(0,j)/120
    assert kernel(3,4) != kernel(0,4)/120
    assert leading_rank(4) == 3
    counts['leading_four_coincidence_checks'] = 6

    total=0
    grid=[Q(k,11) for k in range(11)]
    for xs in itertools.combinations(grid,3):
        for ts in itertools.combinations(grid,2):
            cuts=sorted({bisect_left(xs,t) for t in ts})
            r=len(cuts)-int(0 in cuts and len(xs) in cuts)
            assert r*(gap(list(xs))+gap(list(ts))) >= 1
            total+=1
    counts['circular_gap_rank_checks']=total

    total=0
    for b in (2,6,10,30):
        for m in (-5,0,7,103):
            for num in range(-35,36):
                x=Q(num,13);y=b*x-m
                C=-((-x.numerator)//x.denominator)
                D=-((-y.numerator)//y.denominator)
                e=b*C-D-m
                assert 0<=e<=b-1
                assert D==b*C-(m+e)
                total+=1
    counts['integer_rounding_checks']=total

    bases=[height(2**(a+1))//height(2**a) for a in range(1,101)]
    assert set(bases)=={2,6,10,30}
    total=0
    for M in (1,7,30,210):
        for start in (0,3,21):
            for value in (Q(0),Q(1,97),Q(3,7),Q(96,97)):
                state=value;P=1;s=Q(0)
                for b in bases[start:start+40]:
                    e=(b*state).numerator//(b*state).denominator
                    state=b*state-e
                    P*=b;s+=Q(M*e,P)
                    assert 0<=e<=b-1 and 0<=state<1
                    assert M*value == s+M*state/P
                    total+=1
    counts['greedy_finite_remainder_checks']=total
    # Endpoint is represented by all maximal digits, not by the [0,1) algorithm.
    P=1;s=Q(0)
    for b in bases:
        P*=b;s+=Q(b-1,P)
        assert s == 1-Q(1,P)
    counts['maximal_digit_telescope_checks']=len(bases)
    P=free=1;zeros=0
    for b in bases:
        P*=b
        if b==2:
            zeros+=1
        else:
            free*=b
        assert Q(free,P) == Q(1,2**zeros)
    counts['forced_zero_cover_checks']=len(bases)

    total=0
    for W in (2,6,30,360,10800):
        for H in (1,60,21600):
            for Z in (-3,0,17):
                S=Q(23,19);X=H*S-Z;F=137;Y=W*X-F
                for q in (-19,-2,0,1,2,7,19,1000):
                    error=Q(q*F,W)-q*H*S+q*Z
                    assert error == -Q(q,W)*Y
                    assert circle_dist(Q(q*F,W)-q*H*S) <= abs(Q(q,W)*Y)
                    total+=1
    counts['all_multiplier_shadow_checks']=total

    pool=[0,0,1,2];good=[1,2]
    spread=min(max(circle_dist(Q(q*e,5)) for e in good) for q in range(1,5))
    assert spread == Q(2,5)
    # d < 1/(2 sqrt(5)) iff 20*d*d < 1, tested without roots.
    bad=[sum(20*circle_dist(Q(q*e,5))**2 < 1 for e in pool) for q in range(1,5)]
    union=sum((Q(b*(b-1),4*3) for b in bad),Q(0))
    assert bad==[3,3,3,3] and union==2

    ns=[1,2,3,4,5,6,8,10,16,32,64,128,256,512,1000]
    return {
        'status':'all finite assertions passed',
        'claim_ceiling':'finite exact checks; no Lean build; no parent irrationality claim',
        'checks':counts,
        'total_counted_checks':sum(counts.values()),
        'leading_235_ranks':{str(n):leading_rank(n) for n in ns},
        'spread_counterexample':{'modulus':5,'pool':pool,'good_subset':good,
           'spread':str(spread),'bad_counts':bad,'union_bound_sum':str(union)},
    }


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    report=run();text=json.dumps(report,indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')

if __name__=='__main__':
    main()
