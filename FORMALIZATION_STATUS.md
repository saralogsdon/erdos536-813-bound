# Lean formalization status

## Complete

The Lean development proves the asymptotic `813/1000` upper bound for Erdős Problem #536.

The final theorem is

```lean
Erdos536813.eventually_cardinality_ratio_le_813_1000
```

in `Erdos536813/Final813Bound.lean`. It is imported by the top-level module `Erdos536813.lean`.

For every real `ε > 0`, the theorem provides an `N₀` such that, for every `N ≥ N₀` and every list `A` satisfying `Erdos536.LcmTriangleFreeUpTo N A`,

```text
A.length / N ≤ 813/1000 + ε.
```

## Formalized components

- The `2,3` lattice and fiber reduction.
- The Gamma-free projection baseline.
- Blocking between adjacent `5`-adic slices.
- Annulus and finite two-layer deficit bounds.
- The ten critical finite states.
- Complete `5`-adic core chains and global baseline reindexing.
- Finite and high-scale combined targets.
- Good-core density `4/15`.
- Quotient-fiber reindexing and finite-`N` error estimates.
- The weighted target identity `61/800`.
- The asymptotic global saving `61/3000`.
- The final identity `5/6 - 61/3000 = 813/1000`.

## Verification

GitHub Actions compiles the complete top-level import chain. The formalization contains no intentional `sorry`, `axiom`, or `admit`.

The exact programs `verify_finite.py` and `verify_two_layer_independent.py` remain as independent checks of the finite computation.

## Remaining work

No additional proof step is required for the stated asymptotic theorem.

Possible follow-up work includes independent review, a polished human-readable proof, and an archival release.
