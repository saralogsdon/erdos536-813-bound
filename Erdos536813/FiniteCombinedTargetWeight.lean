import Erdos536813.CombinedTargetDominatesFinite
import Erdos536813.HighScaleTargetWeight

namespace Erdos536813

/-- The rational outer-scale weight of the combined target. -/
def combinedTargetWeight
    (t : Nat) : ℚ :=
  (CombinedCoreTarget t : ℚ) * outerWeight t

/--
At every scale below `120`, the combined target weight is exactly the
previously defined finite weighted deficit.
-/
theorem combinedTargetWeight_eq_finiteWeightedDeficit_of_lt
    {t : Nat}
    (ht : t < 120) :
    combinedTargetWeight t =
      finiteWeightedDeficit t := by

  rw [
    combinedTargetWeight,
    combinedCoreTarget_eq_finiteTargetDeficit_of_lt ht
  ]

  simp [
    outerWeight,
    finiteWeightedDeficit,
    div_eq_mul_inv
  ]

/--
The total combined-target weight over the finite scales `t < 120` is exactly
`1/16`.
-/
theorem finite_combinedTargetWeight_sum :
    (∑ t ∈ Finset.range 120,
      combinedTargetWeight t)
      =
    (1 / 16 : ℚ) := by

  rw [← finite_weighted_deficit_sum]

  apply Finset.sum_congr rfl
  intro t ht

  exact
    combinedTargetWeight_eq_finiteWeightedDeficit_of_lt
      (Finset.mem_range.mp ht)

end Erdos536813
