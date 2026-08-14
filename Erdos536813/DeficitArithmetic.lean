import Mathlib

namespace Erdos536813

/-!
# Exact arithmetic for the 813/1000 bookkeeping

This file contains only the numerical part of the global deficit argument.
It does not yet assert that every fiber realizes the stated deficit; that
combinatorial theorem will be proved separately from the finite two-layer and
large-scale annulus results.

For `t < 120`, the target deficit table is

* deficit 2 on `45..71` and `80..119`;
* deficit 1 on `15..17`, `20..35`, `40..44`, and `72..79`;
* deficit 0 elsewhere.

The weighted finite contribution is exactly `1/16`.

For the high-scale block decomposition, the base `u`-weight is `1/30` and the
extra-block weight is `1/75`. Together with the geometric-series factors used
later, this leads to the total target saving `61/800` and hence the coefficient
`813/1000`.
-/

/-- Target deficit table for the finite range `t < 120`. -/
def finiteTargetDeficit (t : Nat) : Nat :=
  if (45 ≤ t ∧ t ≤ 71) ∨ (80 ≤ t ∧ t ≤ 119) then
    2
  else if
      (15 ≤ t ∧ t ≤ 17) ∨
      (20 ≤ t ∧ t ≤ 35) ∨
      (40 ≤ t ∧ t ≤ 44) ∨
      (72 ≤ t ∧ t ≤ 79) then
    1
  else
    0

/-- The weight `D(t)/(t(t+1))` used in the fiber-counting sum. -/
def finiteWeightedDeficit (t : Nat) : ℚ :=
  (finiteTargetDeficit t : ℚ) /
    ((t : ℚ) * ((t + 1 : Nat) : ℚ))

/-- Exact weighted contribution of all finite scales `t < 120`. -/
theorem finite_weighted_deficit_sum :
    Finset.sum (Finset.range 120) finiteWeightedDeficit = (1 / 16 : ℚ) := by
  native_decide

/-- Basic telescoping weight in the `u` variable. -/
def uWeight (u : Nat) : ℚ :=
  1 / ((u : ℚ) * ((u + 1 : Nat) : ℚ))

/-- Base high-scale block weight. -/
theorem base_u_weight_sum :
    Finset.sum (Finset.Icc 24 119) uWeight = (1 / 30 : ℚ) := by
  native_decide

/-- Extra high-scale block weight. -/
theorem extra_u_weight_sum :
    Finset.sum (Finset.Icc 45 71) uWeight +
      Finset.sum (Finset.Icc 75 119) uWeight =
        (1 / 75 : ℚ) := by
  native_decide

/--
Once the two geometric-series contributions are established as `1/96` and
`1/300`, the total weighted deficit is exactly `61/800`.
-/
theorem total_weighted_deficit_identity :
    (1 / 16 : ℚ) + 1 / 96 + 1 / 300 = 61 / 800 := by
  norm_num

/-- The target improvement over the `5/6` coefficient is exactly `813/1000`. -/
theorem final_coefficient_identity :
    (5 / 6 : ℚ) - (4 / 15) * (61 / 800) = 813 / 1000 := by
  norm_num

end Erdos536813
