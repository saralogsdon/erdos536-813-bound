import Erdos536813.BlockAlignedTruncation

namespace Erdos536813

/--
The normalized global combined target can be written as a sum over all
quotient scales `0..N`.
-/
theorem normalizedGlobalCombinedTarget_eq_quotientSum
    (N : Nat) :
    (GlobalCombinedTargetSum N : ℝ) / (N : ℝ)
      =
    ∑ t ∈ Finset.range (N + 1),
      (CombinedCoreTarget t : ℝ) *
        ((GoodCoreQuotientCount N t : ℝ) /
          (N : ℝ)) := by

  rw [globalCombinedTargetSum_eq_quotientSum]

  push_cast

  rw [Finset.sum_div]

  apply Finset.sum_congr rfl
  intro t ht

  ring

/--
Every truncation through `K ≤ N` is bounded above by the full normalized
global combined target.
-/
theorem truncatedNormalizedTarget_le_normalizedGlobalCombinedTarget
    {N K : Nat}
    (hKN : K ≤ N) :
    TruncatedNormalizedTarget N K
      ≤
    (GlobalCombinedTargetSum N : ℝ) /
      (N : ℝ) := by

  rw [normalizedGlobalCombinedTarget_eq_quotientSum]

  unfold TruncatedNormalizedTarget

  apply Finset.sum_le_sum_of_subset_of_nonneg

  · intro t ht

    have htData :
        1 ≤ t ∧ t ≤ K :=
      Finset.mem_Icc.mp ht

    apply Finset.mem_range.mpr

    omega

  · intro t htRange htNot

    positivity

/--
In particular, every block-aligned truncation whose endpoint lies below
`N` is dominated by the full normalized global target.
-/
theorem blockEndpoint_truncatedNormalizedTarget_le
    {N d : Nat}
    (hEndpoint :
      120 * 5 ^ d - 1 ≤ N) :
    TruncatedNormalizedTarget
        N
        (120 * 5 ^ d - 1)
      ≤
    (GlobalCombinedTargetSum N : ℝ) /
      (N : ℝ) := by

  exact
    truncatedNormalizedTarget_le_normalizedGlobalCombinedTarget
      hEndpoint

end Erdos536813
