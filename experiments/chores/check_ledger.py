"""Exact integer checks of conservative deterministic-chore envelopes."""
import json
from math import comb


for n in range(3, 101):
    ell = (n-1).bit_length()
    W = n*(ell+1)
    B = n*(4**n+2**n)
    E = 3*n-2
    S = (B+n*n+1)*(n+1)**E
    J = (S-1)*(n-1)+1
    H = 2**(n+5)*J*n**3
    V = J*(n**3+n*n)
    L_upper = 14*n*W
    alpha = 2**(n+2)
    assert H > n-1 and H*H > n
    assert H >= J*n*n and H >= 2*alpha and H >= n*n*alpha
    assert H*H-n >= 2*H
    assert 2*(n-1)**n < n**n
    assert H**2 <= 2**(14*W)
    assert S <= 2**(4*W) and J <= 2**(5*W)
    assert J+V*L_upper <= J*2**(3*W)
    for t in range(1, E+1):
        previous = (B+n*n+1)*(n+1)**(t-1)
        current = previous*(n+1)
        assert (current-B)//n >= previous
        assert current//(n+1) >= previous
    core = n*n+n**3*(comb(2*n-2,n-1)-1)
    subcore = n*(2**(n+1)-2*n-2)
    node = (J+V*L_upper)*core+(n+1)*J*n*(n-1)+J*subcore+19*n*2**n
    assert core <= 2**(3*W)
    assert subcore <= 2**W
    assert (n+1)*n*(n-1) <= 2**W
    assert 19*n*2**n <= 2**(2*W)
    assert node <= 2**(12*W)
    assert (2*n-1)*node <= 2**(14*W)
    for b in range(1,n):
        c = n-b
        preparation = 8*(b*b*2**c+c*c*2**b)+2**b+2**c-n-2
        assert preparation <= 19*2**n
        assert 2*2**(c+1) <= alpha and 2*2**(b+1) <= alpha

S_rec = [0,0]
for k in range(2,31):
    S_rec.append(S_rec[k-1]+k*(k-1)+sum(S_rec[1:k-1]))
    assert S_rec[k] == 2**(k+1)-2*k-2

print(json.dumps({"status": "passed", "population_range": [3,100], "subcore_recurrence_range": [2,30], "arithmetic": "exact integers", "least_L": "bounded using the manuscript's 14*n*W upper bound"}, indent=2))
