#!/usr/bin/env python3
"""Exact finite checks of proposed sigma/tau kernel ranks.

The output is finite evidence, not a proof of the formula. The ordinary
proof is supplied separately. No floating-point rank calculation is used.
Requires Python 3.10+ and NumPy. Integers in modular elimination remain < p^2.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from math import gcd
from fractions import Fraction
import numpy as np

PRIMES = (1_000_003, 1_000_033)

def factor(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out

def valuation(n: int, p: int) -> int:
    assert n > 0
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v

def capacity(kind: str, m: int, h: int) -> int:
    return min(m, 2**h if kind == 'sigma' else h+1)

def predicted_rank(kind: str, k: int, e: int) -> int:
    assert kind in ('sigma', 'tau') and k >= 2 and e >= 0
    fac = factor(k)
    result = capacity(kind, e+1, len(fac))
    for t in range(1, e+1):
        for u in range(1, k**t):
            if u % k:
                h = sum(valuation(u,p) >= t*a for p,a in fac.items())
                result += capacity(kind, e-t+1, h)
    return result

def basis_channels(kind: str, k: int, e: int) -> list[tuple[int,int]]:
    fac = factor(k)
    out = [(s,0) for s in range(capacity(kind,e+1,len(fac)))]
    for t in range(1,e+1):
        for u in range(1,k**t):
            if u % k:
                h = sum(valuation(u,p) >= t*a for p,a in fac.items())
                out.extend((t+s,k**s*u) for s in range(capacity(kind,e-t+1,h)))
    assert len(out) == predicted_rank(kind,k,e)
    return out

def tables(limit: int) -> dict[str,np.ndarray]:
    sigma = np.zeros(limit+1,dtype=np.int64)
    tau = np.zeros(limit+1,dtype=np.int64)
    for d in range(1,limit+1):
        sigma[d::d] += d
        tau[d::d] += 1
    return {'sigma':sigma,'tau':tau}

def rank_mod(mat: np.ndarray, p: int) -> int:
    a = mat.copy() % p
    rank = 0
    rows, cols = a.shape
    for col in range(cols):
        positions = np.flatnonzero(a[rank:,col])
        if len(positions) == 0:
            continue
        pivot = rank + int(positions[0])
        a[[rank,pivot]] = a[[pivot,rank]]
        a[rank,col:] = a[rank,col:] * pow(int(a[rank,col]),-1,p) % p
        if rank+1 < rows:
            a[rank+1:,col:] = (a[rank+1:,col:] -
                a[rank+1:,col,None] * a[rank,None,col:]) % p
        rank += 1
        if rank == rows:
            break
    return rank

def rank_series_coefficient(kind: str, k: int, e: int) -> int:
    """Coefficient of the finite rational rank generating function."""
    xs = [p**a for p,a in factor(k).items()]
    h = len(xs)
    full = (1 << h)-1
    cap = lambda j: 2**j if kind == 'sigma' else j+1
    numerator = [0]*(e+1)
    numerator[0] = 1
    if cap(h) <= e:
        numerator[cap(h)] -= 1
    for S in range(1<<h):
        g = [0]*(e+1)
        for T in range(1<<h):
            if S & T != S:
                continue
            K = 1
            for j,x in enumerate(xs):
                if not (T>>j)&1:
                    K *= x
            sign = (-1)**((T^S).bit_count())
            for n in range(1,e+1):
                g[n] += sign*(K-1)*K**(n-1)
        C = cap(S.bit_count())
        for n in range(e+1):
            numerator[n] += g[n] - (g[n-C] if n>=C else 0)
    return sum((e-n+1)*numerator[n] for n in range(e+1))

def run(cases: list[tuple[int,int]], row_multiplier: int = 3) -> dict:
    maxarg = max(k**e * (row_multiplier*max(predicted_rank(f,k,e)
        for f in ('sigma','tau')) + 1) for k,e in cases)
    tab = tables(maxarg)
    results = []
    for k,e in cases:
        allc = [(j,r) for j in range(e+1) for r in range(k**j)]
        for kind in ('sigma','tau'):
            basis = basis_channels(kind,k,e)
            rc = row_multiplier * len(basis)
            ns = np.arange(1,rc+1,dtype=np.int64)
            matrix = np.column_stack([tab[kind][k**j*ns+r] for j,r in allc])
            bas = np.column_stack([tab[kind][k**j*ns+r] for j,r in basis])
            allr = {str(p):rank_mod(matrix,p) for p in PRIMES}
            basr = {str(p):rank_mod(bas,p) for p in PRIMES}
            prediction = predicted_rank(kind,k,e)
            record = dict(function=kind,base=k,depth=e,
                total_channels=len(allc),evaluation_rows=rc,
                predicted_rank=prediction,all_channel_ranks=allr,
                candidate_basis_ranks=basr,
                matched=all(x==prediction for x in [*allr.values(),*basr.values()]))
            if len(factor(k)) == 2 and e >= 1:
                x,y = [p**a for p,a in factor(k).items()]
                bound = 4 if kind == 'sigma' else 3
                closed = k**e+x**(e-1)+y**(e-1)+min(e+1,bound)-3
                assert closed == prediction
                record['two_prime_factor_closed_form'] = closed
            results.append(record)
            print(f'{kind}: base {k}, depth {e}, predicted {prediction}, actual {allr}',flush=True)
    # Integral Boolean inverse, exact rational matrices.
    boolean_checks = []
    for ps in ([2],[2,3],[2,3,5],[3,5,7,11]):
        count = 2**len(ps)
        K = [[Fraction(1) for _ in range(count)] for _ in range(count)]
        Inv = [[1 for _ in range(count)] for _ in range(count)]
        for t in range(count):
            for s in range(count):
                for j,p in enumerate(ps):
                    x,y = (t>>j)&1, (s>>j)&1
                    if x and y: K[t][s] *= Fraction(p,p-1)
                    Inv[t][s] *= [[p,-(p-1)],[-(p-1),p-1]][x][y]
        assert all(sum(Inv[i][t]*K[t][j] for t in range(count)) == int(i==j)
                   for i in range(count) for j in range(count))
        boolean_checks.append({'primes':ps,'dimension':count,'inverse_exact':True})
    # Coefficientwise dilation ladder. b=2,3,5; r=1,...,5; n=1,...,30.
    from math import comb
    count = 0
    for b in (2,3,5):
        for r in range(1,6):
            for n in range(1,31):
                value = sum(Fraction((-1)**(r-j)*comb(r,j)*b**(j*n),
                                     (b**n-1)**r) for j in range(r+1))
                assert value == 1
                count += 1
    generating_checks = 0
    for k in (2,4,6,8,10,12,30):
        for e in range(4):
            for kind in ('sigma','tau'):
                assert rank_series_coefficient(kind,k,e) == predicted_rank(kind,k,e)
                generating_checks += 1
    assert all(r['matched'] for r in results)
    return dict(evidence='Exact finite checks; no all-depth inference from samples.',
        primes=PRIMES,cases=results,boolean_inverse_checks=boolean_checks,
        dilation_coefficient_checks=count,rank_generating_function_checks=generating_checks,
        all_passed=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('rank_and_identity_results.json'))
    args = parser.parse_args()
    cases = [(2,1),(2,4),(4,3),(6,1),(6,2),(6,3),(8,2),(10,2),(12,2),(30,1)]
    result = run(cases)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
