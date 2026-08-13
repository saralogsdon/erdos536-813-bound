# Exact independent full-hypergraph verifier for the two-layer finite lemma.
# Generated during verification of the candidate Erdős #536 bound.

from itertools import combinations
from functools import lru_cache

def L(T):
    if T < 1: return 0
    i = j = 0
    while 2 ** (i + 1) <= T: i += 1
    while 3 ** (j + 1) <= T: j += 1
    return i + j + 1

def D_vertices(T):
    out = []
    i = 0
    while 2**i <= T:
        j = 0
        while 2**i * 3**j <= T:
            out.append((i,j))
            j += 1
        i += 1
    return out

def lcm_exp3(a,b):
    return tuple(max(a[r],b[r]) for r in range(3))

def two_layer_vertices(T):
    return [(i,j,0) for i,j in D_vertices(T)] + [(i,j,1) for i,j in D_vertices(T//5)]

def edges(V):
    ans=[]
    for a,b,c in combinations(range(len(V)),3):
        x,y,z=V[a],V[b],V[c]
        if lcm_exp3(x,y)==lcm_exp3(x,z)==lcm_exp3(y,z):
            ans.append((1<<a)|(1<<b)|(1<<c))
    return ans

def min_hit(n,E):
    inc=[0]*n
    for ei,e in enumerate(E):
        for v in range(n):
            if (e>>v)&1: inc[v] |= 1<<ei
    @lru_cache(None)
    def f(active):
        if active==0: return 0
        ei=(active & -active).bit_length()-1
        e=E[ei]
        return 1+min(f(active & ~inc[v]) for v in range(n) if (e>>v)&1)
    return f((1<<len(E))-1)

for T in [45,48,54,60,64,80,81,90,96,108]:
    V=two_layer_vertices(T); E=edges(V)
    alpha=len(V)-min_hit(len(V),E)
    deficit=L(T)+L(T//5)-alpha
    print(T, deficit)
    assert deficit>=2
print("PASS")
