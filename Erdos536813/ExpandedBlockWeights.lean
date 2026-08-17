import Erdos536813.BlockAlignedWeightLimit

namespace Erdos536813

/--
The actual high-scale weight contained in the first `d` complete
factor-five depth layers.
-/
noncomputable def ExpandedHighBlockWeight
    (d : Nat) : ℝ :=
  ∑ n ∈ Finset.range d,
    ∑ u ∈ Finset.Icc 24 119,
      ∑ t ∈
        Finset.Ico
          (u * 5 ^ (n + 1))
          ((u + 1) * 5 ^ (n + 1)),
        (combinedTargetWeight t : ℝ)

/--
At depth `n+1`, the actual nested block sum is exactly the previously
defined positive-depth contribution.
-/
theorem fixedDepth_combinedTargetWeight_sum_real
    (n : Nat) :
    (∑ u ∈ Finset.Icc 24 119,
      ∑ t ∈
        Finset.Ico
          (u * 5 ^ (n + 1))
          ((u + 1) * 5 ^ (n + 1)),
        (combinedTargetWeight t : ℝ))
      =
    positiveDepthHighContribution n := by

  have hRational :=
    fixedDepth_combinedTargetWeight_sum
      (n + 1)
      (Nat.succ_pos n)

  have hCast :
      (∑ u ∈ Finset.Icc 24 119,
        ∑ t ∈
          Finset.Ico
            (u * 5 ^ (n + 1))
            ((u + 1) * 5 ^ (n + 1)),
          (combinedTargetWeight t : ℝ))
        =
      (((n + 1 : Nat) : ℚ) *
          (1 / (((5 ^ (n + 1) : Nat) : ℚ))) *
          (1 / 30) +
        (1 / (((5 ^ (n + 1) : Nat) : ℚ))) *
          (1 / 75) : ℚ) := by

    exact_mod_cast hRational

  rw [hCast]

  unfold positiveDepthHighContribution

  push_cast

  have hPow :
      (((5 ^ (n + 1) : Nat) : ℚ) : ℝ) =
        (5 : ℝ) ^ (n + 1) := by
    norm_num

  rw [hPow]

  ring

/--
The expanded high-block weight equals the sum of the first `d`
positive-depth contributions.
-/
theorem expandedHighBlockWeight_eq
    (d : Nat) :
    ExpandedHighBlockWeight d =
      ∑ n ∈ Finset.range d,
        positiveDepthHighContribution n := by

  unfold ExpandedHighBlockWeight

  apply Finset.sum_congr rfl
  intro n hn

  exact
    fixedDepth_combinedTargetWeight_sum_real n

/--
The finite contribution plus the expanded high blocks is exactly the
block-aligned weighted target.
-/
theorem finite_add_expandedHighBlockWeight_eq
    (d : Nat) :
    (1 / 16 : ℝ) +
        ExpandedHighBlockWeight d
      =
    BlockAlignedWeightedTarget d := by

  rw [expandedHighBlockWeight_eq]

  rfl

end Erdos536813
