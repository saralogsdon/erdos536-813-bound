# Erdős Problem #536: a candidate 0.813 upper bound

This repository contains a **candidate computer-assisted improvement** for Erdős Problem #536.

For
f(N)=\max\{|A|:A\subseteq\{1,\dots,N\},\; A\text{ contains no three distinct }a,b,c\text{ with }[a,b]=[a,c]=[b,c]\},
the candidate result is
f(N)\le \left(\frac{813}{1000}+o(1)\right)N.

This improves the currently recorded coefficient \(5/6\approx0.833333\) to \(0.813\), **provided the proof and finite verification survive independent review**.

## Status

- The infinite/combinatorial part has a hand proof.
- The delicate finite two-layer lemma is checked by **two independent exact Python programs** using integer arithmetic only.
- The Lean formalization in `Erdos536/` is currently a scaffold: it formalizes definitions and exact arithmetic consequences, but does **not yet formalize the finite stability computation**.
- No claim of final publication-level verification is made yet.

## Reproduce the exact finite checks

Requires Python 3.10+ and no third-party packages.

```bash
python scripts/verify_finite.py
python scripts/verify_two_layer_independent.py
```

The first script checks the annulus bounds, the ten finite two-layer states, and the rational arithmetic. The second independently constructs the full two-layer LCM hypergraph and solves the relevant exact hitting-set problem by recursive integer branching.

The ten critical states are

```text
45, 48, 54, 60, 64, 80, 81, 90, 96, 108.
```

## Proof structure

1. Write each integer uniquely as
   \[
   n=m2^i3^j5^k,\qquad (m,30)=1.
   \]
2. For fixed \(m,k\), selected integers form a \(\Gamma\)-free subset of
   \[
   D(T)=\{(i,j):2^i3^j\le T\}.
   \]
3. The usual projection bound gives
   \[
   |F_k|\le L(T_k)=\lfloor\log_2T_k\rfloor+\lfloor\log_3T_k\rfloor+1,
   \]
   whose global sum recovers the known \(5/6\) bound.
4. A blocking lemma couples adjacent \(5\)-adic slices: an extremal upper slice blocks all nontrivial \(2,3\)-smooth points in the lower inner region.
5. An annulus bound gives additional deficit in the lower slice.
6. Exact finite verification strengthens the two-layer deficit on specified small ranges.
7. Summing forced deficits gives weighted deficit \(61/800\). Since \(m\) coprime to 30 have density \(4/15\),
   \[
   \frac56-\frac4{15}\frac{61}{800}=\frac{813}{1000}.
   \]

See `notes/proof_outline.md` for a more detailed proof outline.

## Lean

This is intended to become a Mathlib project. The current Lean files deliberately do not use `sorry` or introduce axioms; instead, the main arithmetic theorem is stated conditionally on a finite-stability hypothesis. The remaining formalization task is to prove that finite hypothesis by verified computation inside Lean.

Current recommended setup for a Mathlib project is via `lake ... new <project> math`, followed by `lake update` and `lake exe cache get`; see the Lean community installation documentation.

## AI assistance

The mathematical exploration, scripts, proof write-up, and Lean scaffold were prepared with substantial assistance from ChatGPT. The result should be independently checked before being treated as established.
