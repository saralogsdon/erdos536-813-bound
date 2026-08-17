import Erdos536813.NormalizedQuotientDensityApprox

namespace Erdos536813

/--
The normalized actual target contribution from quotient scales `1..K`.
-/
noncomputable def TruncatedNormalizedTarget
    (N K : Nat) : ℝ :=
  ∑ t ∈ Finset.Icc 1 K,
    (CombinedCoreTarget t : ℝ) *
      ((GoodCoreQuotientCount N t : ℝ) /
        (N : ℝ))

/--
The limiting weighted target contribution from quotient scales `1..K`.
-/
noncomputable def TruncatedWeightedTarget
    (K : Nat) : ℝ :=
  ∑ t ∈ Finset.Icc 1 K,
    (CombinedCoreTarget t : ℝ) *
      (outerWeight t : ℝ)

/--
At one positive scale, multiplying by the nonnegative target preserves the
normalized quotient-count error bound.
-/
theorem normalized_target_term_error
    {N t : Nat}
    (hNPos : 0 < N)
    (htPos : 0 < t) :
    |(CombinedCoreTarget t : ℝ) *
          ((GoodCoreQuotientCount N t : ℝ) /
            (N : ℝ)) -
        (4 / 15 : ℝ) *
          ((CombinedCoreTarget t : ℝ) *
            (outerWeight t : ℝ))|
      ≤
    (CombinedCoreTarget t : ℝ) *
      (17 / (N : ℝ)) := by

  have hError :=
    normalized_goodCoreQuotientCount_error
      (N := N) hNPos htPos

  have hTargetNonneg :
      0 ≤ (CombinedCoreTarget t : ℝ) := by
    positivity

  have hIdentity :
      (CombinedCoreTarget t : ℝ) *
          ((GoodCoreQuotientCount N t : ℝ) /
            (N : ℝ)) -
        (4 / 15 : ℝ) *
          ((CombinedCoreTarget t : ℝ) *
            (outerWeight t : ℝ))
        =
      (CombinedCoreTarget t : ℝ) *
        ((GoodCoreQuotientCount N t : ℝ) /
            (N : ℝ) -
          (4 / 15 : ℝ) *
            (outerWeight t : ℝ)) := by
    ring

  rw [hIdentity, abs_mul, abs_of_nonneg hTargetNonneg]

  exact
    mul_le_mul_of_nonneg_left
      hError hTargetNonneg

/--
For every fixed truncation `K`, the normalized actual target differs from
`(4/15)` times its limiting weighted sum by an explicit `O(1/N)` error.
-/
theorem truncatedNormalizedTarget_error
    {N K : Nat}
    (hNPos : 0 < N) :
    |TruncatedNormalizedTarget N K -
        (4 / 15 : ℝ) *
          TruncatedWeightedTarget K|
      ≤
    (17 / (N : ℝ)) *
      (∑ t ∈ Finset.Icc 1 K,
        (CombinedCoreTarget t : ℝ)) := by

  unfold TruncatedNormalizedTarget
    TruncatedWeightedTarget

  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]

  calc
    |∑ t ∈ Finset.Icc 1 K,
        ((CombinedCoreTarget t : ℝ) *
            ((GoodCoreQuotientCount N t : ℝ) /
              (N : ℝ)) -
          (4 / 15 : ℝ) *
            ((CombinedCoreTarget t : ℝ) *
              (outerWeight t : ℝ)))|
        ≤
      ∑ t ∈ Finset.Icc 1 K,
        |(CombinedCoreTarget t : ℝ) *
            ((GoodCoreQuotientCount N t : ℝ) /
              (N : ℝ)) -
          (4 / 15 : ℝ) *
            ((CombinedCoreTarget t : ℝ) *
              (outerWeight t : ℝ))| := by
          exact Finset.abs_sum_le_sum_abs _ _

    _ ≤
      ∑ t ∈ Finset.Icc 1 K,
        (CombinedCoreTarget t : ℝ) *
          (17 / (N : ℝ)) := by
            apply Finset.sum_le_sum
            intro t ht

            have htData :
                1 ≤ t ∧ t ≤ K :=
              Finset.mem_Icc.mp ht

            exact
              normalized_target_term_error
                hNPos htData.1

    _ =
      (17 / (N : ℝ)) *
        (∑ t ∈ Finset.Icc 1 K,
          (CombinedCoreTarget t : ℝ)) := by
            rw [Finset.mul_sum]

            apply Finset.sum_congr rfl
            intro t ht
            ring

end Erdos536813
