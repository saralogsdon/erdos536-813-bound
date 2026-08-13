# Lean formalization status

The current Lean files are a **scaffold, not yet a formal proof of the 0.813 theorem**.

## Present now

- Definitions of admissible sets and the extremal function.
- Exact rational identities yielding `61/800` and `813/1000`.
- No `sorry`, `axiom`, or `admit` is intentionally used.

## Still needed

1. Formalize the 2,3 lattice/fiber reduction.
2. Formalize the Gamma-free projection lemma.
3. Formalize the blocking lemma between 5-adic slices.
4. Formalize the annulus row-counting lemma.
5. Encode the ten finite two-layer states and verify them inside Lean, ideally using `native_decide` or a verified certificate checker.
6. Formalize the asymptotic summation and connect it to `f`.

The Python scripts already give exact reproducible evidence for step 5, but this is not yet kernel-checked by Lean.
