import Erdos536813.HighScaleFixedDepthSum

namespace Erdos536813

/-!
# Summing the positive 5-adic depths

At positive depth `d`, the fixed-depth block calculation gives the closed
form

    (d / 5^d) * (1/30) + (1 / 5^d) * (1/75).

This file reindexes positive depths as `d = n + 1` and proves that the
resulting series has total sum

    1/96 + 1/300 = 11/800.
-/

def positiveDepthContribution (n : Nat) : ℝ :=
  (1 / 30 : ℝ) *
      (((n + 1 : Nat) : ℝ) * (1 / 5 : ℝ) ^ (n + 1)) +
    (1 / 75 : ℝ) *
      ((1 / 5 : ℝ) ^ (n + 1))

/--
The shifted base-depth series still sums to `5/16`:
`sum_{n≥0} (n+1)/5^(n+1) = 5/16`.
-/
theorem shifted_base_depth_geometric_hasSum :
    HasSum
      (fun n : Nat =>
        (((n + 1 : Nat) : ℝ) *
          (1 / 5 : ℝ) ^ (n + 1)))
      (5 / 16 : ℝ) := by

  have h1 :=
    base_depth_geometric_hasSum.mul_left (1 / 5 : ℝ)

  have h2 :=
    extra_depth_geometric_hasSum

  have h12 :
      HasSum
        (fun n : Nat =>
          (1 / 5 : ℝ) *
              ((n : ℝ) * (1 / 5 : ℝ) ^ n) +
            (1 / 5 : ℝ) *
              (1 / 5 : ℝ) ^ n)
        (5 / 16 : ℝ) := by
    have h := h1.add h2
    convert h using 1 <;> norm_num

  have hfun :
      (fun n : Nat =>
        (((n + 1 : Nat) : ℝ) *
          (1 / 5 : ℝ) ^ (n + 1))) =
      (fun n : Nat =>
        (1 / 5 : ℝ) *
            ((n : ℝ) * (1 / 5 : ℝ) ^ n) +
          (1 / 5 : ℝ) *
            (1 / 5 : ℝ) ^ n) := by
    funext n
    push_cast
    rw [pow_succ]
    ring

  rw [hfun]
  exact h12

/--
After multiplying by the terminal base weight `1/30`, the shifted base
contribution is exactly `1/96`.
-/
theorem positive_depth_base_contribution_hasSum :
    HasSum
      (fun n : Nat =>
        (1 / 30 : ℝ) *
          (((n + 1 : Nat) : ℝ) *
            (1 / 5 : ℝ) ^ (n + 1)))
      (1 / 96 : ℝ) := by
  have h :=
    shifted_base_depth_geometric_hasSum.mul_left (1 / 30 : ℝ)
  norm_num at h
  exact h

/--
The shifted terminal-extra contribution is exactly `1/300`.
-/
theorem positive_depth_extra_contribution_hasSum :
    HasSum
      (fun n : Nat =>
        (1 / 75 : ℝ) *
          ((1 / 5 : ℝ) ^ (n + 1)))
      (1 / 300 : ℝ) := by

  have h :=
    extra_high_scale_contribution_hasSum

  have hfun :
      (fun n : Nat =>
        (1 / 75 : ℝ) *
          ((1 / 5 : ℝ) ^ (n + 1))) =
      (fun n : Nat =>
        (1 / 75 : ℝ) *
          ((1 / 5 : ℝ) *
            (1 / 5 : ℝ) ^ n)) := by
    funext n
    rw [pow_succ]
    ring

  rw [hfun]
  exact h

/--
The complete positive-depth high-scale contribution is `11/800`.
-/
theorem positiveDepthContribution_hasSum :
    HasSum
      positiveDepthContribution
      (11 / 800 : ℝ) := by

  have h :=
    positive_depth_base_contribution_hasSum.add
      positive_depth_extra_contribution_hasSum

  unfold positiveDepthContribution
  convert h using 1 <;> norm_num

end Erdos536813
