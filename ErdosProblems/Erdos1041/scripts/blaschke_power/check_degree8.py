#!/usr/bin/env python3
"""Exact rational replay. Python 3.10+, standard library only.

The certificate encloses all seven zeros of F' in disjoint Rouche discs.
At each disc it bounds |F|^2 from below, then checks the displayed rational
lower bound for |r^8 F|^(8/7) by taking seventh powers. No floating-point
number, numerical root finder, or external CAS is used in verification.
Root containment in |z|=1 for F is proved in the accompanying report using
its finite-Blaschke representation; this checker does not replace that proof.
"""
if not __debug__:
    raise RuntimeError('Run without -O: exact certificate assertions must remain enabled.')

from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json


def add(a,b): return a[0]+b[0], a[1]+b[1]
def neg(a): return -a[0],-a[1]
def sub(a,b): return add(a,neg(b))
def mul(a,b): return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]
def scale(a,x): return a[0]*x,a[1]*x
def power(a,n):
    ans=(Q(1),Q(0))
    for _ in range(n): ans=mul(ans,a)
    return ans
def norm_sq(a): return a[0]**2+a[1]**2
def upper_abs(a): return abs(a[0])+abs(a[1])
def lower_abs(a): return max(abs(a[0]),abs(a[1]))
def taylor(coeffs,c):
    """Exact coefficients of p(c+w)."""
    out=[]
    for k in range(len(coeffs)):
        a=(Q(0),Q(0))
        for j in range(k,len(coeffs)):
            a=add(a,scale(power(c,j-k),coeffs[j]*comb(j,k)))
        out.append(a)
    return out

def verify(path):
    data=json.loads(path.read_text())
    a=list(map(Q,data['f_coeffs_ascending']))
    # This identity fixes the polynomial independently of the enclosure rows.
    assert a==[Q(-1),Q(-2),Q(-3,2),Q(-1,2),Q(0),Q(1,2),Q(3,2),Q(2),Q(1)]
    derivative=[j*a[j] for j in range(1,len(a))]
    assert len(data['critical_discs'])==len(derivative)-1==7
    r=Q(data['root_scale']); assert r==Q(999,1000)
    discs=[]; total=Q(0); out=[]
    for k,row in enumerate(data['critical_discs']):
        c=(Q(row['re']),Q(row['im']));eps=Q(row['radius']);assert eps>0
        td=taylor(derivative,c)
        rest=upper_abs(td[0])+sum(upper_abs(td[j])*eps**j for j in range(2,len(td)))
        assert lower_abs(td[1])*eps>rest, ('Rouche',k)
        for c0,e0 in discs:
            assert norm_sq(sub(c,c0))>(eps+e0)**2, ('disjoint',k)
        discs.append((c,eps))
        tf=taylor(a,c)
        err=sum(upper_abs(tf[j])*eps**j for j in range(1,len(tf)))
        lo_re=max(Q(0),abs(tf[0][0])-err)
        lo_im=max(Q(0),abs(tf[0][1])-err)
        lo_sq=lo_re**2+lo_im**2
        y=Q(row['moment_lower']);assert y>0 and lo_sq>0
        # |G(rc)|^2 = r^16 |F(c)|^2; (|G|^(8/7))^7=(|G|^2)^4.
        assert y**7<(r**16*lo_sq)**4, ('moment lower',k)
        total+=y;out.append(str(y))
    assert total>7
    mean=total/7
    assert mean>Q(1075,1000)
    print('PASS: 7 disjoint derivative-root discs, linear Rouche dominance in each.')
    print('PASS: 7 strict rational moment lower bounds for the contracted polynomial.')
    print('PASS: mean |G(c)|^(8/7) >',mean,'> 1.075 > 1.')
    print('Exact individual lower bounds:',', '.join(out))

if __name__=='__main__': verify(Path(__file__).with_name('degree8_certificate.json'))
