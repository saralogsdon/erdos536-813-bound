import Erdos536813.TruncatedTargetDominated

namespace Erdos536813

/--
For any complete block truncation lying below `N`, the normalized global
combined target is bounded below by `(4/15)` times the block-aligned weight,
minus the explicit finite-`N` error.
-/
theorem normalizedGlobalCombinedTarget_lower_of_block
    {N d : Nat}
    (hNPos : 0 < N)
    (hEndpoint :
      120 * 5 ^ d - 1 ≤ N) :
    (4 / 15 : ℝ) *
          BlockAlignedWeightedTarget d
        -
      (17 / (N : ℝ)) *
        (∑ t ∈
          Finset.Icc
            1
            (120 * 5 ^ d - 1),
          (CombinedCoreTarget t : ℝ))
      ≤
    (GlobalCombinedTargetSum N : ℝ) /
      (N : ℝ) := by

  have hError :=
    truncatedNormalizedTarget_error
      (N := N)
      (K := 120 * 5 ^ d - 1)
      hNPos

  have hErrorBounds :=
    abs_le.mp hError

  have hTruncatedLower :
      (4 / 15 : ℝ) *
            TruncatedWeightedTarget
              (120 * 5 ^ d - 1)
          -
        (17 / (N : ℝ)) *
          (∑ t ∈
            Finset.Icc
              1
              (120 * 5 ^ d - 1),
            (CombinedCoreTarget t : ℝ))
        ≤
      TruncatedNormalizedTarget
        N
        (120 * 5 ^ d - 1) := by

    linarith [hErrorBounds.1]

  rw [
    truncatedWeightedTarget_blockEndpoint_eq d
  ] at hTruncatedLower

  have hDominated :
      TruncatedNormalizedTarget
          N
          (120 * 5 ^ d - 1)
        ≤
      (GlobalCombinedTargetSum N : ℝ) /
        (N : ℝ) :=
    blockEndpoint_truncatedNormalizedTarget_le
      hEndpoint

  exact hTruncatedLower.trans hDominated

end Erdos536813
