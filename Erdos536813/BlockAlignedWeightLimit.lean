import Erdos536813.TruncatedTargetApprox

namespace Erdos536813

/--
The weighted target obtained from the finite scales together with the first
`d` complete positive-depth factor-five layers.
-/
noncomputable def BlockAlignedWeightedTarget
    (d : Nat) : ℝ :=
  (1 / 16 : ℝ) +
    ∑ n ∈ Finset.range d,
      positiveDepthHighContribution n

/--
The block-aligned weighted targets converge to the total target weight
`61/800`.
-/
theorem blockAlignedWeightedTarget_tendsto :
    Tendsto
      BlockAlignedWeightedTarget
      atTop
      (nhds (61 / 800 : ℝ)) := by

  have hHigh :
      Tendsto
        (fun d : Nat =>
          ∑ n ∈ Finset.range d,
            positiveDepthHighContribution n)
        atTop
        (nhds (11 / 800 : ℝ)) :=
    positive_depth_high_contribution_hasSum.tendsto_sum_nat

  have hFinite :
      Tendsto
        (fun _d : Nat => (1 / 16 : ℝ))
        atTop
        (nhds (1 / 16 : ℝ)) :=
    tendsto_const_nhds

  have hTotal :=
    hFinite.add hHigh

  convert hTotal using 1
  · funext d
    rfl

  · norm_num

/--
Hence, for every positive error tolerance, some block-aligned partial target
is within that tolerance of `61/800`.
-/
theorem exists_blockAlignedWeightedTarget_close
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ d : Nat,
      |BlockAlignedWeightedTarget d -
          (61 / 800 : ℝ)| < ε := by

  have hEventually :
      ∀ᶠ d : Nat in atTop,
        BlockAlignedWeightedTarget d ∈
          Metric.ball (61 / 800 : ℝ) ε := by

    apply
      (Metric.tendsto_atTop.1
        blockAlignedWeightedTarget_tendsto)
        ε hε

  rcases Filter.eventually_atTop.1 hEventually with
    ⟨d₀, hd₀⟩

  refine ⟨d₀, ?_⟩

  have hd :=
    hd₀ d₀ (le_refl d₀)

  simpa [
    Real.dist_eq,
    abs_sub_comm
  ] using hd

end Erdos536813
