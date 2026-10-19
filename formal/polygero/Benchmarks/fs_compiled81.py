#!/usr/bin/env python3
"""Exact rational 81/80 bound including both adaptive BCS terms.

The maximization is of the proved certificate, not a tightness claim for
Polygero or an attack. Challenge sampling is the exact uniform typed-ROM
sampler of the theorem. Both Merkle commitments use one 256-bit digest ROM.
"""
from fractions import Fraction as F
from math import comb, log2

q = 2**128
digests = 2**256
fc = 32768
cap = 2**120
mu = F(comb(8192, 641), q**65)
ratio = lambda a,t: F(comb(a,t), comb(8192,t))
profile = lambda theta: theta+(1-theta)*(mu+F(1,q))
two = lambda a,b: a+(1-a)*b
work = two(profile(ratio(2713,81)),profile(ratio(2713,80)))
sharp = two(*(profile(max(ratio(1087,t),q*ratio(639,t)/2)) for t in (81,80)))
rho = F(397,100*q)
tau = (1-ratio(2713,80))*mu+F(2,q)+ratio(2713,80)
reserve = F(9*fc,digests)

def A(t,m):
    return t*(t-1)//2+(fc+t)*(2*t+1)+(fc+t)*m

def bcs(n,t):
    return F(A(t,n+4)+A(t,n+3),digests)

def upper(n,t):
    return rho+tau+n*rho+bcs(n,t)

# At fixed total T, the numerator is convex in t, hence its maximum is
# at t=0 or t=T. The former ratio decreases with T. The latter is a
# positive linear term plus a positive reciprocal term and is convex in T.
# Thus only these three endpoints are needed for 1 <= T <= cap.
endpoints = [(1,0),(0,1),(0,cap)]
for name,ref,K in [('working',work,F(1871,1000)),('stronger',sharp,F(2641,1000))]:
    maximum = max(upper(n,t)/((n+t+1)*ref) for n,t in endpoints)
    assert maximum <= K
    print(f'{name}: certificate factor={float(maximum):.12f}; loss={log2(float(maximum)):.9f} bits; rounded factor={float(K):.3f}')
    print(f'  per-work normalized security >= {-log2(float(K*ref)):.9f} bits')
assert reserve <= F(2641,1000)*sharp
assert 8*cap+4*fc+9 <= q
assert 2*rho+tau+2*reserve <= 2*F(2641,1000)*sharp
assert rho+reserve <= F(2641,1000)*sharp
print(f'field={q.bit_length()-1} bits; n=8192; k=512; masks=64; openings=81/80; check fuel={fc}')
print(f'rho*q={float(rho*q):.12f}; tau*q={float(tau*q):.12f}; reserve*q={float(reserve*q):.6e}')
for bits in (32,64,116,120):
    total=2**bits
    for n,t in ((total,0),(total//2,total//2),(0,total)):
        error=bcs(n,t)
        assert error <= F(t,q)+(n+1)*reserve
        penalty=log2(1+float(error/(rho+tau+n*rho)))
        print(f'T=2^{bits}, N/T={n/total:g}: BCS={float(error):.6e}; BCS addition={penalty:.9f} bits')
