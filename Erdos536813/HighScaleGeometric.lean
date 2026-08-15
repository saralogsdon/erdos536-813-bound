import Erdos536813.DeficitArithmetic

namespace Erdos536813

/-!
# Geometric bookkeeping for the high 5-adic scales

The canonical factor-5 decomposition contributes two geometric factors.

* The base deficit at depth `n` is weighted by `n / 5^n`, whose sum over
  `n >= 1` is `5/16`.
* The optional terminal extra deficit is weighted by `1 / 5^n`, whose sum
  over `n >= 1` is `1/4`.

Combined with the already-verified terminal `u`-weights

    1/30   and   1/75,

these give

    (1/30) * (5/16) = 1/96
    (1/75) * (1/4)  = 1/300.

This file proves those analytic/geometric identities over `ℝ`.
-/

/-- The depth-weighted geometric series is `5/16`. -/
theorem base_depth_geometric_hasSum :
    HasSum
      (fun n : Nat => (n : ℝ) * (1 / 5 : ℝ) ^ n)
      (5 / 16 : ℝ) := by
  have hnorm : ‖(1 / 5 : ℝ)‖ < 1 := by
    norm_num [Real.norm_eq_abs]
  convert
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (𝕜 := ℝ) hnorm) using 1 <;> norm_num

/-- The positive-depth geometric series is `1/4`. -/
theorem extra_depth_geometric_hasSum :
    HasSum
      (fun n : Nat => (1 / 5 : ℝ) ^ (n + 1))
      (1 / 4 : ℝ) := by
  have h :=
    (hasSum_geometric_of_lt_one
      (r := (1 / 5 : ℝ))
      (by norm_num)
      (by norm_num)).mul_left (1 / 5 : ℝ)
  convert h using 1
  · ext n
    simp [pow_succ, mul_comm]
  · norm_num

/-- The base high-scale contribution is exactly `1/96`. -/
theorem base_high_scale_contribution_hasSum :
    HasSum
      (fun n : Nat =>
        (1 / 30 : ℝ) *
          ((n : ℝ) * (1 / 5 : ℝ) ^ n))
      (1 / 96 : ℝ) := by
  have h :=
    base_depth_geometric_hasSum.mul_left (1 / 30 : ℝ)
  convert h using 1 <;> norm_num

/-- The terminal-extra high-scale contribution is exactly `1/300`. -/
theorem extra_high_scale_contribution_hasSum :
    HasSum
      (fun n : Nat =>
        (1 / 75 : ℝ) *
          (1 / 5 : ℝ) ^ (n + 1))
      (1 / 300 : ℝ) := by
  have h :=
    extra_depth_geometric_hasSum.mul_left (1 / 75 : ℝ)
  convert h using 1 <;> norm_num

/-- Together the two high-scale contributions are `11/800`. -/
theorem high_scale_weighted_deficit_identity :
    (1 / 96 : ℝ) + 1 / 300 = 11 / 800 := by
  norm_num

/-- Adding the finite-scale `1/16` contribution gives the target `61/800`. -/
theorem total_weighted_deficit_real_identity :
    (1 / 16 : ℝ) + 1 / 96 + 1 / 300 = 61 / 800 := by
  norm_num

end Erdos536813
