
"""
Exact verifier for the computer-assisted finite lemmas used in the candidate
Erdos #536 bound

    f(N) <= (813/1000 + o(1)) N.

No floating-point optimization is used in the finite checks.  The program
enumerates all relevant subsets exactly using integer bitmasks.

What is checked:
1. Annulus lemma on all finite board states needed below T=729:
      h(T) <= L(T)-2 on the ranges needed for a 1-unit slice deficit,
      h(T) <= L(T)-3 for every 120 <= T <= 728.
   For T >= 729 the proof is by the general row/double-row argument, not by code.

2. Exact two-layer stability:
      d_0 + d_1 >= 2
   for 45 <= T <= 71 and 80 <= T <= 119.
   It suffices to test ten critical board states.

3. Exact rational arithmetic for the final asymptotic coefficient:
      5/6 - (4/15)*(61/800) = 813/1000.
"""

from itertools import combinations
from fractions import Fraction


def L(T):
    if T < 1:
        return 0
    i = 0
    while 2 ** (i + 1) <= T:
        i += 1
    j = 0
    while 3 ** (j + 1) <= T:
        j += 1
    return i + j + 1


def D_vertices(T):
    out = []
    i = 0
    while 2 ** i <= T:
        j = 0
        while 2 ** i * 3 ** j <= T:
            out.append((i, j))
            j += 1
        i += 1
    return out


def lcm_exp(a, b):
    return (max(a[0], b[0]), max(a[1], b[1]))


def bad3(a, b, c):
    return lcm_exp(a, b) == lcm_exp(a, c) == lcm_exp(b, c)


def bad_masks(V):
    masks = []
    for e in combinations(range(len(V)), 3):
        a, b, c = (V[i] for i in e)
        if bad3(a, b, c):
            masks.append(sum(1 << i for i in e))
    return masks


def gamma_free_subsets(V, size):
    forbidden = bad_masks(V)
    ans = []
    for C in combinations(range(len(V)), size):
        mask = sum(1 << i for i in C)
        if all(mask & e != e for e in forbidden):
            ans.append(mask)
    return ans


def exact_max_gamma_free(V):
    forbidden = bad_masks(V)
    best = 0
    for mask in range(1 << len(V)):
        c = mask.bit_count()
        if c <= best:
            continue
        if all(mask & e != e for e in forbidden):
            best = c
    return best


def annulus_vertices(T):
    # T/5 < 2^i 3^j <= T, written without floating point.
    return [
        v for v in D_vertices(T)
        if 5 * (2 ** v[0]) * (3 ** v[1]) > T
    ]


def cross_block_mask(V_upper, upper_mask, V_lower):
    inds = [i for i in range(len(V_upper)) if (upper_mask >> i) & 1]
    blocked = 0
    for ui, vi in combinations(inds, 2):
        u, v = V_upper[ui], V_upper[vi]
        M = lcm_exp(u, v)
        for ci, c in enumerate(V_lower):
            if M == lcm_exp(u, c) == lcm_exp(v, c):
                blocked |= 1 << ci
    return blocked


def compatible_pair_exists(V_upper, uppers, V_lower, lowers):
    for um in uppers:
        blocked = cross_block_mask(V_upper, um, V_lower)
        for lm in lowers:
            if lm & blocked == 0:
                return True
    return False


def verify_two_layer_deficit_two(T):
    S = T // 5
    V0 = D_vertices(T)
    V1 = D_vertices(S)
    l0, l1 = L(T), L(S)

    lower_0 = gamma_free_subsets(V0, l0)
    lower_1 = gamma_free_subsets(V0, l0 - 1)
    upper_0 = gamma_free_subsets(V1, l1)
    upper_1 = gamma_free_subsets(V1, l1 - 1)

    # Total deficit <= 1 has only these three possibilities:
    # (d_lower, d_upper) = (0,0), (1,0), (0,1).
    bad00 = compatible_pair_exists(V1, upper_0, V0, lower_0)
    bad10 = compatible_pair_exists(V1, upper_0, V0, lower_1)
    bad01 = compatible_pair_exists(V1, upper_1, V0, lower_0)

    return not (bad00 or bad10 or bad01), (
        len(lower_0), len(lower_1), len(upper_0), len(upper_1)
    )


def smooth_23_values(limit):
    vals = set()
    i = 0
    while 2 ** i <= limit:
        j = 0
        while 2 ** i * 3 ** j <= limit:
            vals.add(2 ** i * 3 ** j)
            j += 1
        i += 1
    return vals


def critical_annulus_states(lo, hi):
    # Annulus membership of v changes only when T reaches v or 5v.
    vals = smooth_23_values(hi)
    crit = {lo}
    for v in vals:
        for x in (v, 5 * v):
            if lo <= x <= hi:
                crit.add(x)
    return sorted(crit)


def main():
    print("Checking annulus states...")

    # Exact finite verification for the ranges used in the proof.
    # For T >= 729, the general row argument gives L(T)-h(T) >= 3.
    ann_crit = critical_annulus_states(15, 728)
    ann_def = {}
    for T in ann_crit:
        V = annulus_vertices(T)
        h = exact_max_gamma_free(V)
        ann_def[T] = L(T) - h

    # Board and L(T) are constant between successive critical states, so
    # checking the start of each interval suffices.
    def deficit_at(T):
        start = max(x for x in ann_crit if x <= T)
        return ann_def[start]

    for T in range(15, 729):
        need1 = (15 <= T <= 17) or (20 <= T <= 35) or (T >= 40)
        if need1:
            assert deficit_at(T) >= 2, (T, deficit_at(T))
        if T >= 120:
            assert deficit_at(T) >= 3, (T, deficit_at(T))

    print("  annulus finite checks: PASS")

    print("Checking exact two-layer stability states...")
    critical = [45, 48, 54, 60, 64, 80, 81, 90, 96, 108]
    for T in critical:
        ok, counts = verify_two_layer_deficit_two(T)
        assert ok, T
        print(
            f"  T={T:3d}: PASS; "
            f"(lower extremal, lower deficit-1, upper extremal, upper deficit-1)"
            f" = {counts}"
        )

    print("Checking final rational arithmetic...")
    S_small = Fraction(1, 16)
    S_tail = Fraction(1, 96) + Fraction(1, 300)
    S = S_small + S_tail
    coeff = Fraction(5, 6) - Fraction(4, 15) * S

    assert S == Fraction(61, 800)
    assert coeff == Fraction(813, 1000)

    print(f"  weighted deficit S = {S}")
    print(f"  final coefficient   = {coeff} = {float(coeff):.12f}")
    print()
    print("ALL EXACT FINITE CHECKS PASSED.")


if __name__ == "__main__":
    main()
