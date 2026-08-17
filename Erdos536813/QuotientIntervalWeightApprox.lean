import Erdos536813.NatDivRealApprox

namespace Erdos536813

/-- The natural-number length of the quotient interval for scale `t`. -/
def QuotientIntervalLength
    (N t : Nat) : Nat :=
  N / t - N / (t + 1)

/-- The rational outer weight, cast to `ℝ`, is the expected telescoping term. -/
theorem outerWeight_cast_real_eq
    {t : Nat}
    (htPos : 0 < t) :
    (outerWeight t : ℝ) =
      1 / (t : ℝ) -
        1 / ((t + 1 : Nat) : ℝ) := by

  have htNe :
      (t : ℝ) ≠ 0 := by
    positivity

  have htSuccNe :
      ((t + 1 : Nat) : ℝ) ≠ 0 := by
    positivity

  unfold outerWeight
  push_cast

  field_simp [htNe, htSuccNe]
  ring

/--
Before normalizing by `N`, the quotient-interval length differs from
`N * outerWeight t` by at most two.
-/
theorem quotientIntervalLength_sub_weight_abs_le_two
    {N t : Nat}
    (htPos : 0 < t) :
    |(QuotientIntervalLength N t : ℝ) -
        (N : ℝ) * (outerWeight t : ℝ)| ≤ 2 := by

  have hDivLe :
      N / (t + 1) ≤ N / t := by

    have hMul :
        (N / (t + 1)) * (t + 1) ≤ N :=
      Nat.div_mul_le_self N (t + 1)

    have hMul' :
        (N / (t + 1)) * t ≤ N := by
      exact Nat.le_trans
        (Nat.mul_le_mul_left
          (N / (t + 1))
          (Nat.le_succ t))
        hMul

    exact
      (Nat.le_div_iff_mul_le htPos).mpr
        hMul'

  have hUpperError :
      |((N / t : Nat) : ℝ) -
          (N : ℝ) / (t : ℝ)| ≤ 1 :=
    natDiv_cast_sub_realDiv_abs_le_one
      htPos

  have hLowerError :
      |((N / (t + 1) : Nat) : ℝ) -
          (N : ℝ) /
            ((t + 1 : Nat) : ℝ)| ≤ 1 :=
    natDiv_cast_sub_realDiv_abs_le_one
      (Nat.succ_pos t)

  rw [QuotientIntervalLength]
  rw [Nat.cast_sub hDivLe]
  rw [outerWeight_cast_real_eq htPos]

  have hIdentity :
      ((N / t : Nat) : ℝ) -
          ((N / (t + 1) : Nat) : ℝ) -
          (N : ℝ) *
            (1 / (t : ℝ) -
              1 / ((t + 1 : Nat) : ℝ))
        =
      (((N / t : Nat) : ℝ) -
          (N : ℝ) / (t : ℝ)) -
        (((N / (t + 1) : Nat) : ℝ) -
          (N : ℝ) /
            ((t + 1 : Nat) : ℝ)) := by
    ring

  rw [hIdentity]

  calc
    |(((N / t : Nat) : ℝ) -
          (N : ℝ) / (t : ℝ)) -
        (((N / (t + 1) : Nat) : ℝ) -
          (N : ℝ) /
            ((t + 1 : Nat) : ℝ))|
        ≤
      |((N / t : Nat) : ℝ) -
          (N : ℝ) / (t : ℝ)| +
        |((N / (t + 1) : Nat) : ℝ) -
          (N : ℝ) /
            ((t + 1 : Nat) : ℝ)| :=
      abs_sub _ _

    _ ≤ 2 := by
      linarith

/--
After division by positive `N`, the normalized quotient-interval length is
within `2/N` of `outerWeight t`.
-/
theorem normalized_quotientIntervalWeight_error
    {N t : Nat}
    (hNPos : 0 < N)
    (htPos : 0 < t) :
    |(QuotientIntervalLength N t : ℝ) / (N : ℝ) -
        (outerWeight t : ℝ)|
      ≤
    2 / (N : ℝ) := by

  have hNReal :
      0 < (N : ℝ) := by
    exact_mod_cast hNPos

  have hError :=
    quotientIntervalLength_sub_weight_abs_le_two
      (N := N) htPos

  have hIdentity :
      (QuotientIntervalLength N t : ℝ) /
          (N : ℝ) -
          (outerWeight t : ℝ)
        =
      ((QuotientIntervalLength N t : ℝ) -
          (N : ℝ) * (outerWeight t : ℝ)) /
        (N : ℝ) := by
    field_simp
    ring

  rw [hIdentity, abs_div, abs_of_pos hNReal]

  exact
    div_le_div_of_nonneg_right
      hError
      (le_of_lt hNReal)

end Erdos536813
