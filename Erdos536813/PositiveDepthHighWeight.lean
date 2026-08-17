import Erdos536813.CombinedFiveBlockWeight

namespace Erdos536813

/--
The real-valued high-scale contribution at positive depth `n + 1`.
-/
def positiveDepthHighContribution
    (n : Nat) : ℝ :=
  ((n + 1 : Nat) : ℝ) *
      (1 / 5 : ℝ) ^ (n + 1) *
      (1 / 30) +
    (1 / 5 : ℝ) ^ (n + 1) *
      (1 / 75)

/--
The shifted depth-weighted geometric series still sums to `5/16`, since its
missing depth-zero term is zero.
-/
theorem positive_depth_base_geometric_hasSum :
    HasSum
      (fun n : Nat =>
        ((n + 1 : Nat) : ℝ) *
          (1 / 5 : ℝ) ^ (n + 1))
      (5 / 16 : ℝ) := by

  have hGeometric :
      HasSum
        (fun n : Nat => (1 / 5 : ℝ) ^ n)
        (5 / 4 : ℝ) := by
    have h :=
      hasSum_geometric_of_lt_one
        (r := (1 / 5 : ℝ))
        (by norm_num)
        (by norm_num)
    norm_num at h
    exact h

  have hAdded :=
    base_depth_geometric_hasSum.add hGeometric

  have hScaled :=
    hAdded.mul_left (1 / 5 : ℝ)

  convert hScaled using 1
  · funext n
    rw [pow_succ]
    push_cast
    ring
  · norm_num

/-- The base part of the positive-depth contribution sums to `1/96`. -/
theorem positive_depth_base_contribution_hasSum :
    HasSum
      (fun n : Nat =>
        ((n + 1 : Nat) : ℝ) *
          (1 / 5 : ℝ) ^ (n + 1) *
          (1 / 30))
      (1 / 96 : ℝ) := by

  have h :=
    positive_depth_base_geometric_hasSum.mul_left
      (1 / 30 : ℝ)

  convert h using 1
  · funext n
    ring
  · norm_num

/-- The terminal-extra part over positive depths sums to `1/300`. -/
theorem positive_depth_extra_contribution_hasSum :
    HasSum
      (fun n : Nat =>
        (1 / 5 : ℝ) ^ (n + 1) *
          (1 / 75))
      (1 / 300 : ℝ) := by

  have h :=
    extra_depth_geometric_hasSum.mul_left
      (1 / 75 : ℝ)

  convert h using 1
  · funext n
    rw [pow_succ]
    ring
  · norm_num

/--
The total weighted high-scale contribution over every positive depth is
exactly `11/800`.
-/
theorem positive_depth_high_contribution_hasSum :
    HasSum
      positiveDepthHighContribution
      (11 / 800 : ℝ) := by

  have h :=
    positive_depth_base_contribution_hasSum.add
      positive_depth_extra_contribution_hasSum

  simpa [positiveDepthHighContribution] using h

end Erdos536813
