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

noncomputable def positiveDepthContribution (n : Nat) : ℝ :=
  (1 / 30 : ℝ) *
      (((n + 1 : Nat) : ℝ) * (1 / 5 : ℝ) ^ (n + 1)) +
    (1 / 75 : ℝ) *
      ((1 / 5 : ℝ) ^ (n + 1))

theorem shifted_base_depth_geometric_hasSum :
    HasSum
      (fun n : Nat =>
        (((n + 1 : Nat) : ℝ) *
          (1 / 5 : ℝ) ^ (n + 1)))
      (5 / 16 : ℝ) := by

  have h1 :
      HasSum
        (fun n : Nat =>
          (1 / 5 : ℝ) *
            ((n : ℝ) * (1 / 5 : ℝ) ^ n))
        ((1 / 5 : ℝ) * (5 / 16 : ℝ)) :=
    base_depth_geometric_hasSum.mul_left (1 / 5 : ℝ)

  have h2 :
      HasSum
        (fun n : Nat =>
          (1 / 5 : ℝ) * (1 / 5 : ℝ) ^ n)
        (1 / 4 : ℝ) :=
    extra_depth_geometric_hasSum

  have h :
      HasSum
        (fun n : Nat =>
          (1 / 5 : ℝ) *
              ((n : ℝ) * (1 / 5 : ℝ) ^ n) +
            (1 / 5 : ℝ) *
              (1 / 5 : ℝ) ^ n)
        ((1 / 5 : ℝ) * (5 / 16 : ℝ) + 1 / 4) :=
    h1.add h2

  have hval :
      (1 / 5 : ℝ) * (5 / 16 : ℝ) + 1 / 4 = 5 / 16 := by
    norm_num

  rw [hval] at h

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
  exact h

theorem positive_depth_base_contribution_hasSum :
    HasSum
      (fun n : Nat =>
        (1 / 30 : ℝ) *
          (((n + 1 : Nat) : ℝ) *
            (1 / 5 : ℝ) ^ (n + 1)))
      (1 / 96 : ℝ) := by

  have h :
      HasSum
        (fun n : Nat =>
          (1 / 30 : ℝ) *
            (((n + 1 : Nat) : ℝ) *
              (1 / 5 : ℝ) ^ (n + 1)))
        ((1 / 30 : ℝ) * (5 / 16 : ℝ)) :=
    shifted_base_depth_geometric_hasSum.mul_left (1 / 30 : ℝ)

  have hval :
      (1 / 30 : ℝ) * (5 / 16 : ℝ) = 1 / 96 := by
    norm_num

  rw [hval] at h
  exact h

theorem positive_depth_extra_contribution_hasSum :
    HasSum
      (fun n : Nat =>
        (1 / 75 : ℝ) *
          ((1 / 5 : ℝ) ^ (n + 1)))
      (1 / 300 : ℝ) := by

  have h :
      HasSum
        (fun n : Nat =>
          (1 / 75 : ℝ) *
            ((1 / 5 : ℝ) *
              (1 / 5 : ℝ) ^ n))
        (1 / 300 : ℝ) :=
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

theorem positiveDepthContribution_hasSum :
    HasSum
      positiveDepthContribution
      (11 / 800 : ℝ) := by

  have h :
      HasSum
        (fun n : Nat =>
          (1 / 30 : ℝ) *
              (((n + 1 : Nat) : ℝ) *
                (1 / 5 : ℝ) ^ (n + 1)) +
            (1 / 75 : ℝ) *
              ((1 / 5 : ℝ) ^ (n + 1)))
        ((1 / 96 : ℝ) + 1 / 300) :=
    positive_depth_base_contribution_hasSum.add
      positive_depth_extra_contribution_hasSum

  have hval :
      (1 / 96 : ℝ) + 1 / 300 = 11 / 800 := by
    norm_num

  rw [hval] at h

  change
    HasSum
      (fun n : Nat =>
        (1 / 30 : ℝ) *
            (((n + 1 : Nat) : ℝ) *
              (1 / 5 : ℝ) ^ (n + 1)) +
          (1 / 75 : ℝ) *
            ((1 / 5 : ℝ) ^ (n + 1)))
      (11 / 800 : ℝ)

  exact h

end Erdos536813
