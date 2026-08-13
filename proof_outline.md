# Proof outline for the candidate bound 813/1000

## 1. Problem

Let `f(N)` denote the largest size of a set `A ⊆ {1,...,N}` with no three distinct elements `a,b,c` satisfying

`lcm(a,b) = lcm(a,c) = lcm(b,c)`.

The goal of this repository is to verify the candidate bound

`f(N) ≤ (813/1000 + o(1)) N`.

## 2. 2,3,5-adic fibers

Write uniquely

`n = m 2^i 3^j 5^k`, with `(m,30)=1`.

Fix `m`. For the `k`-th 5-adic slice define

`T_k = floor(N/(m 5^k))`

and identify the selected integers with points

`F_k ⊆ D(T_k) = {(i,j): 2^i 3^j ≤ T_k}`.

A northeast corner `(i,j),(i-a,j),(i,j-b)` would give three integers with identical pairwise LCM, so every `F_k` is Gamma-free.

## 3. Projection bound

For Gamma-free `F ⊆ D(T)`, the standard projection to the two coordinate axes is injective. Thus

`|F| ≤ L(T) := floor(log_2 T)+floor(log_3 T)+1`.

Summing `L(T_k)` over all `m,k` gives the number of integers at most `N` not divisible by 6, hence the baseline bound

`f(N) ≤ N-floor(N/6) = (5/6+o(1))N`.

Define slice deficit

`d_k = L(T_k)-|F_k|`.

The new argument gives lower bounds on the sum of the `d_k`.

## 4. Blocking lemma

Suppose `F ⊆ D(S)` is Gamma-free and `|F|=L(S)`.

First, `1∈F`: adding the lattice origin cannot create a corner, so a maximum family must contain it.

For every nontrivial 2,3-smooth `c≤S`:

- If `c∈F`, then `{5,5c,c}` is an LCM triangle.
- If `c∉F`, then maximality of `F` implies adding `c` creates a corner with some `u,v∈F`. Multiplying `u,v` by 5 gives `{5u,5v,c}`, again an LCM triangle.

Therefore an extremal upper 5-adic slice forbids every nontrivial 2,3-smooth point in the lower inner region.

## 5. Annulus lemma

Define

`R(T)={2^i3^j : T/5 < 2^i3^j ≤ T}`

and let `h(T)` be the largest Gamma-free subset of `R(T)`.

The required estimate is

`h(T) ≤ L(T)-3` for `T≥120`.

For sufficiently large T this follows from the row structure of the multiplicative annulus. Each row contains at most two points because the annulus has multiplicative width 5 and three consecutive powers of 3 span a factor 9. Rows containing two selected points cannot have equal or consecutive right endpoints. Therefore, if

`I=floor(log_2 T)`, `J=floor(log_3 T)`,

then

`h(T) ≤ I+1+ceil(J/2)`.

For `J≥6` this is at most `L(T)-3`. The finite remainder is checked exactly by `scripts/verify_finite.py`.

Hence, for `T_k≥120`,

`d_{k+1}=0 => d_k≥2`.

## 6. Exact finite two-layer stability

The stronger inequality

`d_k+d_{k+1}≥2`

is needed on

`45≤T_k≤71` and `80≤T_k≤119`.

The boards change only when T crosses `2^i3^j` or `5*2^i3^j`, so it suffices to check

`45,48,54,60,64,80,81,90,96,108`.

Two independent exact implementations verify these states:

- `scripts/verify_finite.py`: enumerates extremal and deficit-one Gamma-free slices by integer bitmasks.
- `scripts/verify_two_layer_independent.py`: builds the full two-layer LCM hypergraph and solves an exact minimum hitting-set problem recursively.

No floating point or MILP solver is used.

## 7. Summation

For `t<120`, the forced deficit has harmonic weight

`1/16`.

For the infinite tail, repeated 5-adic scaling contributes

`1/96 + 1/300`.

Thus the total weighted deficit is

`S = 1/16 + 1/96 + 1/300 = 61/800`.

The values of `m` coprime to 30 have density

`phi(30)/30 = 4/15`.

Therefore the density saving from the 5/6 baseline is

`(4/15)(61/800)=61/3000`,

and

`5/6 - 61/3000 = 813/1000`.

Hence the candidate theorem is

`f(N) ≤ (813/1000 + o(1))N`.

## 8. What remains to formalize

The main remaining Lean target is the finite two-layer stability proposition. The cleanest route is likely to define the finite boards and forbidden triples as decidable finite structures and discharge the ten states with `native_decide` or a small verified certificate checker.
