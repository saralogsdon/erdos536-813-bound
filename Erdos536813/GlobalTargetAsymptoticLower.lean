import Erdos536813.FixedBlockGlobalLower

namespace Erdos536813

/--
The normalized global combined target is eventually at least
`61/3000 - ε`.
-/
theorem eventually_normalizedGlobalCombinedTarget_ge_61_3000
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : Nat,
      ∀ N ≥ N₀,
        (61 / 3000 : ℝ) - ε
          ≤
        (GlobalCombinedTargetSum N : ℝ) /
          (N : ℝ) := by

  have hHalf :
      0 < ε / 2 := by
    positivity

  rcases
    exists_blockAlignedWeightedTarget_close
      hHalf
    with
      ⟨d, hd⟩

  have hdBounds :=
    abs_lt.mp hd

  have hBlockLower :
      (61 / 800 : ℝ) - ε / 2
        <
      BlockAlignedWeightedTarget d := by

    linarith [hdBounds.1]

  rcases
    eventually_normalizedGlobalCombinedTarget_ge_block
      d hHalf
    with
      ⟨N₀, hN₀⟩

  refine ⟨N₀, ?_⟩

  intro N hN

  have hGlobal :=
    hN₀ N hN

  have hCoefficient :
      (4 / 15 : ℝ) *
          (61 / 800 : ℝ)
        =
      (61 / 3000 : ℝ) := by
    norm_num

  rw [← hCoefficient]

  linarith

end Erdos536813
