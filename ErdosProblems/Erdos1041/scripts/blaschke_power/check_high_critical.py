#!/usr/bin/env python3
"""Rational replay of the degree-24 high-critical counterexample.

Python 3.10+, standard library only. No numerical root solver is imported.
The helper functions perform complex arithmetic as pairs of Fractions.
The report supplies the analytic Rouche and circle-root interpretation.
"""
if not __debug__:
    raise RuntimeError('Run without -O: exact certificate assertions must remain enabled.')

from fractions import Fraction as Q
from pathlib import Path
from math import comb
import json
from check_degree8 import taylor, upper_abs, lower_abs, norm_sq, sub


def verify(path):
    data=json.loads(path.read_text())
    N=data['N']; b=Q(data['b']); r=Q(data['root_scale'])
    assert N==12 and b==Q(1,120) and r==Q(999999999,10**9)
    n=2*N; m=n-1
    # Construct A^N-D^N directly, independently of enclosure data.
    a=[Q(0) for _ in range(n+1)]
    for j in range(N+1):
        a[N+j]+=comb(N,j)*b**(N-j)
        a[j]-=comb(N,j)*b**j
    derivative=[j*a[j] for j in range(1,n+1)]
    assert len(data['critical_discs'])==m
    discs=[];total=Q(0)
    for k,row in enumerate(data['critical_discs']):
        c=(Q(row['re']),Q(row['im']));eps=Q(row['radius']);assert eps>0
        td=taylor(derivative,c)
        tail=upper_abs(td[0])+sum(upper_abs(td[j])*eps**j for j in range(2,len(td)))
        assert lower_abs(td[1])*eps>tail,('Rouche',k)
        for c0,e0 in discs:
            assert norm_sq(sub(c,c0))>(eps+e0)**2,('disjoint',k)
        discs.append((c,eps))
        tf=taylor(a,c)
        err=sum(upper_abs(tf[j])*eps**j for j in range(1,len(tf)))
        # Bounds for G(rc)=r^n F(c), including |G(rc)+1|<1/12.
        centre=(r**n*tf[0][0],r**n*tf[0][1]); error=r**n*err
        ub_shifted_sq=(abs(centre[0]+1)+error)**2+(abs(centre[1])+error)**2
        assert ub_shifted_sq<Q(1,12)**2,('critical value disc',k)
        lo_sq=max(Q(0),abs(centre[0])-error)**2+max(Q(0),abs(centre[1])-error)**2
        y=Q(row['moment_lower']);assert y>0
        assert y**m<lo_sq**4,('moment lower',k)
        total+=y
    mean=total/m
    assert mean>Q(40001,40000)
    # Exact implications of the common value disc.
    assert Q(11,12)>Q(13,25)
    assert 2*Q(1,12)/Q(11,12)==Q(2,11)
    assert 1+Q(2,11)<Q(4,3)
    print('PASS: 23 disjoint derivative-root discs, one critical point in each.')
    print('PASS: every critical value of G lies in |v+1|<1/12.')
    print('Hence mu>11/12>13/25; every pair satisfies |v_i/v_j-1|<2/11.')
    print('Hence no selected critical value passes the radius-4/3 test at any centre in [0,1].')
    print('PASS: mean |G(c)|^(8/23) >',mean,'>40001/40000>1.')

if __name__=='__main__': verify(Path(__file__).with_name('high_critical_certificate.json'))
