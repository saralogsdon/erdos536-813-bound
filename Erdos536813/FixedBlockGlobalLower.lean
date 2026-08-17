import Erdos536813.GlobalTargetBlockLower

namespace Erdos536813

/-- The unweighted target mass appearing in the error for block depth `d`. -/
noncomputable def BlockTargetMass
    (d : Nat) : ℝ :=
  ∑ t ∈
    Finset.Icc
      1
      (120 * 5 ^ d - 1),
    (CombinedCoreTarget t : ℝ)

/-- The explicit finite-`N` error attached to block depth `d`. -/
noncomputable def BlockFiniteError
    (N d : Nat) : ℝ :=
  (17 / (N : ℝ)) *
    BlockTargetMass d

/-- For fixed block depth, the finite-`N` error tends to zero. -/
theorem blockFiniteError_tendsto_zero
    (d : Nat) :
    Tendsto
      (fun N : Nat =>
        BlockFiniteError N d)
      atTop
      (nhds 0) := by

  have hBase :
      Tendsto
        (fun N : Nat =>
          (17 * BlockTargetMass d) /
            (N : ℝ) ^ 1)
        atTop
        (nhds 0) :=
    tendsto_const_div_pow
      (17 * BlockTargetMass d)
      1
      (by norm_num)

  convert hBase using 1

  funext N

  unfold BlockFiniteError

  simp [pow_one]

  ring

/--
For every fixed complete block truncation and every positive tolerance,
all sufficiently large `N` have normalized global target at least the
corresponding block weight minus that tolerance.
-/
theorem eventually_normalizedGlobalCombinedTarget_ge_block
    (d : Nat)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : Nat,
      ∀ N ≥ N₀,
        (4 / 15 : ℝ) *
              BlockAlignedWeightedTarget d
            - ε
          ≤
        (GlobalCombinedTargetSum N : ℝ) /
          (N : ℝ) := by

  have hEventually :
      ∀ᶠ N : Nat in atTop,
        BlockFiniteError N d ∈
          Metric.ball (0 : ℝ) ε := by

    apply
      (Metric.tendsto_atTop.1
        (blockFiniteError_tendsto_zero d))
        ε hε

  rcases Filter.eventually_atTop.1 hEventually with
    ⟨M, hM⟩

  let K : Nat :=
    120 * 5 ^ d - 1

  let N₀ : Nat :=
    max M (max K 1)

  refine ⟨N₀, ?_⟩

  intro N hN

  have hNM :
      M ≤ N := by
    dsimp [N₀] at hN
    omega

  have hNK :
      K ≤ N := by
    dsimp [N₀] at hN
    omega

  have hNPos :
      0 < N := by
    dsimp [N₀] at hN
    omega

  have hErrorBall :=
    hM N hNM

  have hErrorNonneg :
      0 ≤ BlockFiniteError N d := by
    unfold BlockFiniteError BlockTargetMass
    positivity

  have hErrorSmall :
      BlockFiniteError N d < ε := by
    simpa [
      Real.dist_eq,
      abs_of_nonneg hErrorNonneg
    ] using hErrorBall

  have hLower :=
    normalizedGlobalCombinedTarget_lower_of_block
      (N := N)
      (d := d)
      hNPos
      (by simpa [K] using hNK)

  change
    (4 / 15 : ℝ) *
          BlockAlignedWeightedTarget d
        -
      BlockFiniteError N d
      ≤
    (GlobalCombinedTargetSum N : ℝ) /
      (N : ℝ) at hLower

  linarith

end Erdos536813
