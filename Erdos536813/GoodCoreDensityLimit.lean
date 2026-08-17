import Erdos536813.GoodCoreDensityError

namespace Erdos536813

/--
The proportion of good cores approaches `4/15`, in explicit epsilon form.
The previously proved uniform error bound gives a concrete proof.
-/
theorem goodCoreCount_ratio_tends_to_density
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ X₀ : Nat,
      ∀ X : Nat,
        X₀ ≤ X →
        0 < X →
        |(GoodCoreCount X : ℝ) / (X : ℝ) -
            (4 / 15 : ℝ)| < ε := by

  obtain ⟨X₀, hX₀⟩ :=
    exists_nat_gt (8 / ε)

  refine ⟨X₀, ?_⟩

  intro X hX₀X hXPos

  have hXReal :
      0 < (X : ℝ) := by
    exact_mod_cast hXPos

  have hX₀XReal :
      (X₀ : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hX₀X

  have hEightX₀ :
      8 < ε * (X₀ : ℝ) := by
    have :=
      (div_lt_iff₀ hε).mp hX₀
    nlinarith

  have hEightX :
      8 < ε * (X : ℝ) := by
    nlinarith

  have hEightDiv :
      (8 : ℝ) / (X : ℝ) < ε := by
    exact
      (div_lt_iff₀ hXReal).mpr
        (by nlinarith)

  have hError :
      |(GoodCoreCount X : ℝ) -
          (4 / 15 : ℝ) * X| ≤ 8 :=
    goodCoreCount_sub_density_bound X

  have hIdentity :
      (GoodCoreCount X : ℝ) / (X : ℝ) -
          (4 / 15 : ℝ)
        =
      ((GoodCoreCount X : ℝ) -
          (4 / 15 : ℝ) * X) /
        (X : ℝ) := by
    field_simp
    ring

  rw [hIdentity, abs_div, abs_of_pos hXReal]

  have hDivBound :
      |(GoodCoreCount X : ℝ) -
          (4 / 15 : ℝ) * X| /
          (X : ℝ)
        ≤
      8 / (X : ℝ) := by
    exact
      div_le_div_of_nonneg_right
        hError
        (le_of_lt hXReal)

  exact lt_of_le_of_lt hDivBound hEightDiv

end Erdos536813
