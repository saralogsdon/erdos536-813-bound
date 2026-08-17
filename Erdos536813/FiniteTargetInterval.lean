import Erdos536813.CombinedTargetWeightReal

namespace Erdos536813

/-- The combined target weight at the artificial scale `0` vanishes. -/
theorem combinedTargetWeight_zero :
    combinedTargetWeight 0 = 0 := by

  simp [combinedTargetWeight, outerWeight]

/--
The scales `1..119` have the same total weight as `range 120`,
because the only additional scale is `0`, whose weight vanishes.
-/
theorem finite_combinedTargetWeight_Icc_sum_real :
    (∑ t ∈ Finset.Icc 1 119,
      (combinedTargetWeight t : ℝ))
      =
    (∑ t ∈ Finset.range 120,
      (combinedTargetWeight t : ℝ)) := by

  apply Finset.sum_subset

  · intro t ht

    have htData :
        1 ≤ t ∧ t ≤ 119 :=
      Finset.mem_Icc.mp ht

    exact
      Finset.mem_range.mpr (by omega)

  · intro t htRange htNot

    have htUpper : t < 120 :=
      Finset.mem_range.mp htRange

    have htZero : t = 0 := by
      by_contra hne

      have htPos : 1 ≤ t :=
        Nat.one_le_iff_ne_zero.mpr hne

      have htIcc :
          t ∈ Finset.Icc 1 119 := by
        apply Finset.mem_Icc.mpr
        omega

      exact htNot htIcc

    subst t

    norm_num [combinedTargetWeight_zero]

/-- The truncated weighted target through scale `119` is exactly `1/16`. -/
theorem truncatedWeightedTarget_119_eq :
    TruncatedWeightedTarget 119 =
      (1 / 16 : ℝ) := by

  rw [
    truncatedWeightedTarget_eq_combinedTargetWeight_sum,
    finite_combinedTargetWeight_Icc_sum_real,
    finite_combinedTargetWeight_sum_real
  ]

/--
The finite truncation through `119`, together with the first `d` complete
high-depth layers, is exactly the block-aligned weighted target.
-/
theorem truncatedWeightedTarget_119_add_expandedHighBlockWeight_eq
    (d : Nat) :
    TruncatedWeightedTarget 119 +
        ExpandedHighBlockWeight d
      =
    BlockAlignedWeightedTarget d := by

  rw [truncatedWeightedTarget_119_eq]

  exact finite_add_expandedHighBlockWeight_eq d

end Erdos536813
