# Erdős Problem #536: a Lean-verified 0.813 asymptotic upper bound

This repository contains a Lean formalization of an improved asymptotic upper bound for Erdős Problem #536.

Let `f(N)` be the maximum size of a set `A ⊆ {1, ..., N}` containing no three distinct elements `a, b, c` such that

```text
lcm(a,b) = lcm(a,c) = lcm(b,c).
```

The formalized result is

```text
f(N) ≤ (813/1000 + o(1))N.
```

Equivalently, for every real `ε > 0`, all sufficiently large `N` satisfy

```text
|A| / N ≤ 813/1000 + ε
```

for every admissible `A`.

The final Lean theorem is

```lean
Erdos536813.eventually_cardinality_ratio_le_813_1000
```

in `Erdos536813/Final813Bound.lean`.

## Status

- The full combinatorial, finite, global-summation, and asymptotic argument is formalized in Lean.
- The development contains no intentional `sorry`, `axiom`, or `admit`.
- GitHub Actions compiles the complete import chain through `Erdos536813.lean`.
- Two independent exact Python programs remain available as additional checks of the finite computation.
- Independent mathematical and code review is welcome.

## Main theorem

```lean
theorem eventually_cardinality_ratio_le_813_1000
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : Nat,
      ∀ N ≥ N₀,
        ∀ A : List Nat,
          Erdos536.LcmTriangleFreeUpTo N A →
          (A.length : ℝ) / (N : ℝ)
            ≤
          (813 / 1000 : ℝ) + ε
```

## Proof structure

1. Decompose integers into cores coprime to `30` and powers of `2`, `3`, and `5`.
2. Organize selected integers into `2,3`-lattice fibers and `5`-adic chains.
3. Apply the projection baseline, whose global density gives the classical coefficient `5/6`.
4. Prove blocking and annulus deficit bounds between adjacent `5`-adic slices.
5. Verify the ten critical finite two-layer states inside Lean.
6. Combine the finite and high-scale targets into a global target saving.
7. Prove the good-core density and quotient-fiber error estimates.
8. Evaluate the total weighted deficit as `61/800`.
9. Conclude from

```text
5/6 - (4/15)(61/800) = 813/1000.
```

See `proof_outline.md` for a longer mathematical overview.

## Building

With Lean and Lake installed, run:

```bash
lake update
lake exe cache get
lake build
```

The top-level module `Erdos536813.lean` imports the completed formalization.

## Independent finite checks

The Python checks require Python 3.10 or later and no third-party packages:

```bash
python verify_finite.py
python verify_two_layer_independent.py
```

The ten critical states are:

```text
45, 48, 54, 60, 64, 80, 81, 90, 96, 108
```

These scripts provide independent exact-arithmetic checks; the corresponding finite results are also proved inside Lean.

## AI assistance

The mathematical exploration, scripts, proof write-up, and Lean formalization were prepared with substantial assistance from ChatGPT. Independent human review is recommended before the result is treated as externally validated.
