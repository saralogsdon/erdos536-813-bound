import Erdos536813.GlobalTargetAsymptoticLower

namespace Erdos536813

/-- The remaining normalized floor error `1/N` eventually becomes arbitrarily small. -/
theorem eventually_one_div_nat_lt
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : Nat,
      ∀ N ≥ N₀,
        0 < N ∧
          1 / (N : ℝ) < ε := by

  have hTendsto :
      Tendsto
        (fun N : Nat =>
          (1 : ℝ) / (N : ℝ) ^ 1)
        atTop
        (nhds 0) :=
    tendsto_const_div_pow
      (1 : ℝ)
      1
      (by norm_num)

  have hEventually :
      ∀ᶠ N : Nat in atTop,
        (1 : ℝ) / (N : ℝ) ^ 1 ∈
          Metric.ball (0 : ℝ) ε := by

    apply
      (Metric.tendsto_atTop.1 hTendsto)
        ε hε

  rcases Filter.eventually_atTop.1 hEventually with
    ⟨M, hM⟩

  let N₀ : Nat := max M 1

  refine ⟨N₀, ?_⟩

  intro N hN

  have hNM :
      M ≤ N := by
    dsimp [N₀] at hN
    omega

  have hNPos :
      0 < N := by
    dsimp [N₀] at hN
    omega

  have hBall :=
    hM N hNM

  have hNonneg :
      0 ≤ (1 : ℝ) / (N : ℝ) ^ 1 := by
    positivity

  have hSmall :
      (1 : ℝ) / (N : ℝ) ^ 1 < ε := by

    simpa [
      Real.dist_eq,
      abs_of_nonneg hNonneg
    ] using hBall

  refine ⟨hNPos, ?_⟩

  simpa [pow_one] using hSmall

/--
The natural-number baseline `N - N/6`, after normalization, is at most
`5/6 + 1/N`.
-/
theorem normalized_fiveSix_baseline_le
    {N : Nat}
    (hNPos : 0 < N) :
    ((N - N / 6 : Nat) : ℝ) /
        (N : ℝ)
      ≤
    (5 / 6 : ℝ) +
      1 / (N : ℝ) := by

  have hDivError :=
    natDiv_cast_sub_realDiv_abs_lt_one
      (N := N)
      (t := 6)
      (by norm_num)

  have hDivBounds :=
    abs_lt.mp hDivError

  have hFloorLower :
      (N : ℝ) / 6 - 1
        <
      ((N / 6 : Nat) : ℝ) := by
    linarith [hDivBounds.1]

  have hSubCast :
      ((N - N / 6 : Nat) : ℝ)
        =
      (N : ℝ) -
        ((N / 6 : Nat) : ℝ) := by

    rw [
      Nat.cast_sub
        (Nat.div_le_self N 6)
    ]

  have hBaseline :
      ((N - N / 6 : Nat) : ℝ)
        ≤
      (5 / 6 : ℝ) * (N : ℝ) + 1 := by

    rw [hSubCast]
    linarith

  have hNReal :
      0 < (N : ℝ) := by
    exact_mod_cast hNPos

  have hNormalized :=
    (div_le_div_iff₀ hNReal).2 hBaseline

  calc
    ((N - N / 6 : Nat) : ℝ) /
          (N : ℝ)
        ≤
      ((5 / 6 : ℝ) * (N : ℝ) + 1) /
          (N : ℝ) := hNormalized

    _ =
      (5 / 6 : ℝ) +
        1 / (N : ℝ) := by
          field_simp
          ring

/--
Final asymptotic `813/1000` theorem.

For every positive `ε`, all sufficiently large triangle-free lists have
normalized cardinality at most `813/1000 + ε`.
-/
theorem eventually_cardinality_ratio_le_813_1000
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : Nat,
      ∀ N ≥ N₀,
        ∀ A : List Nat,
          Erdos536.LcmTriangleFreeUpTo N A →
          (A.length : ℝ) / (N : ℝ)
            ≤
          (813 / 1000 : ℝ) + ε := by

  have hHalf :
      0 < ε / 2 := by
    positivity

  rcases
    eventually_normalizedGlobalCombinedTarget_ge_61_3000
      hHalf
    with
      ⟨N₁, hN₁⟩

  rcases
    eventually_one_div_nat_lt
      hHalf
    with
      ⟨N₂, hN₂⟩

  let N₀ : Nat := max N₁ N₂

  refine ⟨N₀, ?_⟩

  intro N hN A hA

  have hNN₁ :
      N₁ ≤ N := by
    dsimp [N₀] at hN
    omega

  have hNN₂ :
      N₂ ≤ N := by
    dsimp [N₀] at hN
    omega

  have hSaving :=
    hN₁ N hNN₁

  have hSmallData :=
    hN₂ N hNN₂

  have hNPos :
      0 < N :=
    hSmallData.1

  have hOneSmall :
      1 / (N : ℝ) < ε / 2 :=
    hSmallData.2

  have hStructuralNat :=
    card_add_globalCombinedTarget_le_fiveSixBound
      (A := A)
      (N := N)
      hA

  have hStructuralReal :
      (A.length : ℝ) +
          (GlobalCombinedTargetSum N : ℝ)
        ≤
      ((N - N / 6 : Nat) : ℝ) := by

    exact_mod_cast hStructuralNat

  have hNReal :
      0 < (N : ℝ) := by
    exact_mod_cast hNPos

  have hStructuralNormalized :=
    (div_le_div_iff₀ hNReal).2
      hStructuralReal

  rw [add_div] at hStructuralNormalized

  have hBaseline :=
    normalized_fiveSix_baseline_le
      hNPos

  have hCoefficient :
      (5 / 6 : ℝ) -
          (61 / 3000 : ℝ)
        =
      (813 / 1000 : ℝ) := by
    norm_num

  rw [← hCoefficient]

  linarith

end Erdos536813
