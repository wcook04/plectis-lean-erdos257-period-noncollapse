#!/usr/bin/env python3
"""Exact spot checks for numerical examples in the proposed short-note edits.

These checks do not prove the universal basis or rank-one theorems.
Requires only Python 3.10+ standard library.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import argparse


def phi_table(n: int) -> list[int]:
    a = list(range(n+1))
    for p in range(2,n+1):
        if a[p] == p:
            for k in range(p,n+1,p):
                a[k] -= a[k]//p
    return a


def mobius(n: int) -> int:
    sign, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n>1 else sign


def check() -> dict:
    ph = phi_table(1000)
    D = sum((ph[14+j]-ph[13+j])*2**(15-j) for j in range(16))
    assert D == -143140 and D % 2**16 == 53468
    B = 12+1+16+2
    assert B < D % 2**16 < 2**16-B
    identities = 0
    for n in range(100):
        assert ph[8*n+2] == ph[4*n+1]
        assert ph[8*n+4] == 2*ph[2*n+1]
        assert ph[8*n+6] == ph[4*n+3]
        assert ph[4*n+3] % 2 == 0
        identities += 4
    num = sum(F(mobius(d),(2**d-1)**3) for d in range(1,6))
    den = sum(F(mobius(d),(2**d-1)**4) for d in range(1,6))
    Q = num*num/den
    assert Q == F(35076077250375200,37573118933633199)
    # phi(n) <= n gives this exact upper tail bound for n > N.
    N = 80
    S_low = sum(F(ph[n],2**n) for n in range(1,N+1))
    S_high = S_low+F(N+2,2**N)
    gap_lower = Q-(S_high-F(1,2))
    gap_upper = Q-(S_low-F(1,2))
    assert F(21,320) < gap_lower <= gap_upper < F(1,15)
    return dict(evidence='Finite exact checks only.',
        seed=dict(h=1,N=12,L=16,D=D,residue=D%2**16,B=B,passed=True),
        reduction_and_parity_checks=identities,
        rank_one=dict(e=1,Y=5,quotient=str(Q),
            gap_interval=[str(gap_lower),str(gap_upper)],
            interval_strictly_between=['21/320','1/15']),all_passed=True)

if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('note_facts_results.json'))
    args=parser.parse_args()
    args.output.write_text(json.dumps(check(),indent=2)+'\n')
    print('Exact seed, 400 reduction/parity identities, and rank-one gap interval passed.')
