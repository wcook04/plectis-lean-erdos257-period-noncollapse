#!/usr/bin/env python3
"""Exact certificates for factorial-channel moment ideals (round 5).

Python 3.10+; standard library only. No floating point, CAS, network, or Lean.
Run: ./repo-python Erdos68/scripts/check_moment_saturation.py --quick
     ./repo-python Erdos68/scripts/check_moment_saturation.py --max-d 24 --limit 800

The finite stopping test is proved in mathematical_refinements.md. A finite
scan alone is NOT the certificate: every row also checks g | lcm(1,...,N+1).
The script independently constructs an admissible primitive vector attaining
its asserted minimum positive moment and checks every cancelled channel.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from functools import lru_cache
from math import gcd, lcm, isqrt
from pathlib import Path


def require(test: bool, message: str) -> None:
    if not test:
        raise ArithmeticError(message)


def egcd(a: int, b: int) -> tuple[int, int, int]:
    """Return nonnegative g and x,y such that ax+by=g, including zeros."""
    aa, bb = abs(a), abs(b)
    x0, x1, y0, y1 = 1, 0, 0, 1
    while bb:
        k = aa // bb
        aa, bb = bb, aa - k * bb
        x0, x1 = x1, x0 - k * x1
        y0, y1 = y1, y0 - k * y1
    return aa, x0 * (1 if a >= 0 else -1), y0 * (1 if b >= 0 else -1)


def add_scaled(target: dict[int, int], source: dict[int, int], scale: int) -> None:
    for j, c in source.items():
        target[j] = target.get(j, 0) + scale * c
        if target[j] == 0:
            del target[j]


def certificates(max_d: int, limit: int) -> dict:
    require(2 <= max_d < limit, 'Require 2 <= max-d < limit.')
    fac = [1] * (limit + 2)
    pref_lcm = [1] * (limit + 2)
    for n in range(1, limit + 2):
        fac[n] = n * fac[n-1]
        pref_lcm[n] = lcm(pref_lcm[n-1], n)
    proper = [[] for _ in range(limit + 1)]
    for d in range(2, limit // 2 + 1):
        for n in range(2*d, limit+1, d):
            proper[n].append(d)

    def w(d: int, n: int) -> int:
        denominator = fac[d] ** (n // d)
        require(fac[n] % denominator == 0, 'Nonintegral channel coefficient.')
        return fac[n] // denominator

    u = [0] * (limit + 1)
    u[2] = 2
    transport_checks = 0
    for n in range(3, limit + 1):
        u[n] = -sum(w(d,n)*u[d] for d in proper[n])
        for d in proper[n]:
            require((w(d,n)*pref_lcm[d]) % pref_lcm[n] == 0,
                    f'Lcm transport fails at ({d},{n}).')
            transport_checks += 1
        require(u[n] % pref_lcm[n] == 0, f'Lcm envelope fails at {n}.')
        require(u[n] == 0 if n % 2 else u[n] < 0, f'Parity/sign fails at {n}.')

    def exact_valuation(value: int, prime: int) -> int:
        require(value != 0, 'Prime-power coefficient unexpectedly zero.')
        exponent = 0
        while value % prime == 0:
            value //= prime
            exponent += 1
        return exponent

    prime_power_tests = 0
    k = 1
    while 2**k <= limit:
        require(exact_valuation(u[2**k], 2) == k, '2-power valuation identity fails.')
        prime_power_tests += 1
        k += 1
    for prime in range(3, limit//2 + 1, 2):
        if any(prime % d == 0 for d in range(2,isqrt(prime)+1)):
            continue
        k = 1
        while 2*prime**k <= limit:
            require(exact_valuation(u[2*prime**k], prime) == 2*k,
                    f'Odd-prime-power valuation identity fails at {prime}^{k}.')
            prime_power_tests += 1
            k += 1

    @lru_cache(None)
    def unit(n: int) -> dict[int, int]:
        value = {n-1:n, n:-1}
        for d in proper[n]:
            add_scaled(value, unit(d), -w(d,n))
        require(value.get(1,0) == u[n], f'Unit/scalar recurrence disagree at {n}.')
        return value

    rows = []
    LD = 1
    for D in range(2, max_d+1):
        LD = lcm(LD, fac[D]-1)
        K = {1:LD}
        for d in range(2,D+1):
            add_scaled(K, unit(d), -(LD // (fac[d]-1)))
        a = K.get(1,0)
        require(a < 0, f'Unexpected index-1 coefficient at D={D}.')
        g = 0
        bezout: dict[int,int] = {}
        stop = None
        last_change = None
        for N in range(D+1,limit+1):
            new_g, x, y = egcd(g,u[N])
            if new_g != g:
                bezout = {n:x*b for n,b in bezout.items() if x*b}
                if y:
                    bezout[N] = y
                last_change = N
            # If g is unchanged the old Bezout certificate is still valid.
            g = new_g
            if g and pref_lcm[N+1] % g == 0:
                stop = N
                break
        if stop is None:
            raise ArithmeticError(f'No stopping certificate by {limit} for D={D}; increase --limit.')
        require(stop <= D**4, 'Polynomial index horizon violated.')
        require(sum(b*u[n] for n,b in bezout.items()) == g, 'Bezout identity fails.')
        require(all(u[n] % g == 0 for n in range(D+1,stop+1)), 'Finite gcd divisor fails.')
        t = g // gcd(g,a)
        require((t*a) % g == 0, 'Moment multiplier does not remove support obstruction.')
        z = {n:-(t*a//g)*b for n,b in bezout.items() if b}
        lam: dict[int,int] = {}
        add_scaled(lam,K,t)
        for n, b in z.items():
            add_scaled(lam,unit(n),b)
        require(lam.get(1,0) == 0 and min(lam)>=2, 'Forbidden index 1 remains.')
        moment = sum(c*fac[n] for n,c in lam.items())
        require(moment == t*LD > 0, 'Wrong moment.')
        for d in range(2,D+1):
            require(sum(c*w(d,n) for n,c in lam.items()) == 0,
                    f'Channel {d} fails at D={D}.')
        content = 0
        for c in lam.values():
            content = gcd(content,abs(c))
        require(content == 1, 'Minimum-moment witness is not primitive.')
        require(moment % (12*LD) == 0, 'Known support-sensitive divisibility fails.')
        # Independent finite-horizon scalar check beyond the certified stop.
        require(all(u[n] % g == 0 for n in range(stop+1,limit+1)), 'Post-stop diagnostic fails.')
        rows.append({
            'D': D, 'certification_cutoff_N':stop, 'polynomial_horizon_D4':D**4, 'last_gcd_change':last_change,
            'tail_gcd':str(g), 'Lambda_N_plus_1_mod_g':pref_lcm[stop+1] % g,
            'a_D':str(a), 'L_D':str(LD), 'minimum_moment_multiplier':str(t),
            'minimum_positive_moment':str(moment),
            'bezout_coefficients':{str(n):str(c) for n,c in sorted(bezout.items())},
            'witness_upper_support':max(lam),
            'primitive_witness':{str(n):str(c) for n,c in sorted(lam.items())},
            'checked_channels':list(range(2,D+1)), 'content':content,
        })
    # Certified p-adic limits: the tail after p**k-1 lies in p**k Z_p.
    # Multiplication by p**E clears the finitely many early p-denominators.
    padic_rows = []
    def vp_nonzero(value: int, prime: int) -> int:
        require(value != 0, 'Valuation requested at zero.')
        exponent = 0
        while value % prime == 0:
            value //= prime
            exponent += 1
        return exponent
    for prime in range(2,min(150,limit+1)):
        if any(prime % d == 0 for d in range(2,isqrt(prime)+1)):
            continue
        E = max([0]+[vp_nonzero(fac[n]-1,prime) for n in range(2,prime)])
        precision, cutoff = 1, prime-1
        while cutoff <= limit:
            modulus = prime**(E+precision)
            residue = prime**E
            for n in range(2,cutoff+1):
                denominator = fac[n]-1
                exponent = vp_nonzero(denominator,prime)
                require(exponent <= E, 'Early-denominator exponent bound failed.')
                unit_den = denominator // prime**exponent
                residue -= prime**(E-exponent)*u[n]*pow(unit_den,-1,modulus)
                residue %= modulus
            if residue:
                padic_rows.append({
                    'prime':prime, 'tail_precision':precision, 'cutoff':cutoff,
                    'clearing_exponent':E, 'scaled_residue':str(residue),
                    'modulus':str(modulus),
                    'beta_valuation':vp_nonzero(residue,prime)-E,
                })
                break
            precision += 1
            cutoff = prime**precision-1
        else:
            padic_rows.append({'prime':prime,'status':'undetermined within the scalar limit'})
    scalar_payload = '\n'.join(f'{n}:{u[n]}' for n in range(2,limit+1)).encode()
    return {
        'description':'Exact finite certificates for unrestricted-support channel moment ideals',
        'evidence':'Ordinary stopping theorem plus exact standard-library arithmetic; not a Lean replay',
        'max_D':max_d,'scalar_check_limit':limit,
        'transport_identity_tests':transport_checks, 'prime_power_valuation_tests':prime_power_tests,
        'scalar_values_sha256':hashlib.sha256(scalar_payload).hexdigest(),
        'rows':rows,
        'padic_limit_certificates':padic_rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-d',type=int,default=24)
    parser.add_argument('--limit',type=int,default=800)
    parser.add_argument('--quick',action='store_true',
                        help='Regression: D<=5 through index 40, covering mu_4=1380.')
    parser.add_argument('--output',type=Path,default=Path('moment_saturation_certificates.json'))
    args = parser.parse_args()
    if args.quick:
        args.max_d, args.limit = 5, 40
    result = certificates(args.max_d,args.limit)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('D  tail gcd         multiplier    stop  witness support')
    for row in result['rows']:
        print(f"{row['D']:2} {row['tail_gcd']:>16} {row['minimum_moment_multiplier']:>11} "
              f"{row['certification_cutoff_N']:7} {row['witness_upper_support']:8}")
    print(f"PASS: {len(result['rows'])} unrestricted-support certificates; "
          f"{result['transport_identity_tests']} finite transport tests.")
    print(args.output)

if __name__ == '__main__':
    main()
