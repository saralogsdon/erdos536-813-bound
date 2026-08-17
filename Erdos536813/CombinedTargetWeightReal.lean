import Erdos536813.ExpandedBlockWeights

namespace Erdos536813

/--
Casting `combinedTargetWeight` from the rationals to the reals gives the
real-valued summand used by `TruncatedWeightedTarget`.
-/
theorem combinedTargetWeight_cast_real
    (t : Nat) :
    (combinedTargetWeight t : ℝ) =
      (CombinedCoreTarget t : ℝ) *
        (outerWeight t : ℝ) := by

  unfold combinedTargetWeight
  push_cast
  rfl

/--
The truncated weighted target can equivalently be written using
`combinedTargetWeight`.
-/
theorem truncatedWeightedTarget_eq_combinedTargetWeight_sum
    (K : Nat) :
    TruncatedWeightedTarget K =
      ∑ t ∈ Finset.Icc 1 K,
        (combinedTargetWeight t : ℝ) := by

  unfold TruncatedWeightedTarget

  apply Finset.sum_congr rfl
  intro t ht

  exact
    (combinedTargetWeight_cast_real t).symm

/--
The finite combined-target weight remains exactly `1/16` after passing
from the rationals to the reals.
-/
theorem finite_combinedTargetWeight_sum_real :
    (∑ t ∈ Finset.range 120,
      (combinedTargetWeight t : ℝ))
      =
    (1 / 16 : ℝ) := by

  exact_mod_cast finite_combinedTargetWeight_sum

/--
The expanded high-block weight can be written directly using the
real-valued target-times-outer-weight summands.
-/
theorem expandedHighBlockWeight_eq_target_weight_sum
    (d : Nat) :
    ExpandedHighBlockWeight d =
      ∑ n ∈ Finset.range d,
        ∑ u ∈ Finset.Icc 24 119,
          ∑ t ∈
            Finset.Ico
              (u * 5 ^ (n + 1))
              ((u + 1) * 5 ^ (n + 1)),
            (CombinedCoreTarget t : ℝ) *
              (outerWeight t : ℝ) := by

  unfold ExpandedHighBlockWeight

  apply Finset.sum_congr rfl
  intro n hn

  apply Finset.sum_congr rfl
  intro u hu

  apply Finset.sum_congr rfl
  intro t ht

  exact combinedTargetWeight_cast_real t

end Erdos536813
