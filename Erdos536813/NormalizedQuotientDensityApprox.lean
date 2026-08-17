import Erdos536813.QuotientIntervalWeightApprox

namespace Erdos536813

/--
For every positive `N` and positive quotient scale `t`, the normalized
good-core quotient count differs from `(4/15) * outerWeight t` by at most
`17/N`.
-/
theorem normalized_goodCoreQuotientCount_error
    {N t : Nat}
    (hNPos : 0 < N)
    (htPos : 0 < t) :
    |(GoodCoreQuotientCount N t : ℝ) / (N : ℝ) -
        (4 / 15 : ℝ) * (outerWeight t : ℝ)|
      ≤
    17 / (N : ℝ) := by

  have hNReal :
      0 < (N : ℝ) := by
    exact_mod_cast hNPos

  have hCountError :
      |(GoodCoreQuotientCount N t : ℝ) -
          (4 / 15 : ℝ) *
            (QuotientIntervalLength N t : ℝ)| ≤ 16 := by
    simpa [QuotientIntervalLength] using
      goodCoreQuotientCount_density_error
        (N := N) htPos

  have hFloorError :
      |(QuotientIntervalLength N t : ℝ) /
            (N : ℝ) -
          (outerWeight t : ℝ)|
        ≤
      2 / (N : ℝ) :=
    normalized_quotientIntervalWeight_error
      hNPos htPos

  have hCountErrorNormalized :
      |((GoodCoreQuotientCount N t : ℝ) -
          (4 / 15 : ℝ) *
            (QuotientIntervalLength N t : ℝ)) /
          (N : ℝ)|
        ≤
      16 / (N : ℝ) := by

    rw [abs_div, abs_of_pos hNReal]

    exact
      div_le_div_of_nonneg_right
        hCountError
        (le_of_lt hNReal)

  have hFloorErrorScaled :
      |(4 / 15 : ℝ) *
          ((QuotientIntervalLength N t : ℝ) /
              (N : ℝ) -
            (outerWeight t : ℝ))|
        ≤
      (4 / 15 : ℝ) *
        (2 / (N : ℝ)) := by

    rw [abs_mul]

    have hDensityAbs :
        |(4 / 15 : ℝ)| = 4 / 15 := by
      norm_num

    rw [hDensityAbs]

    exact
      mul_le_mul_of_nonneg_left
        hFloorError
        (by norm_num)

  have hIdentity :
      (GoodCoreQuotientCount N t : ℝ) /
          (N : ℝ) -
          (4 / 15 : ℝ) *
            (outerWeight t : ℝ)
        =
      ((GoodCoreQuotientCount N t : ℝ) -
          (4 / 15 : ℝ) *
            (QuotientIntervalLength N t : ℝ)) /
          (N : ℝ) +
        (4 / 15 : ℝ) *
          ((QuotientIntervalLength N t : ℝ) /
              (N : ℝ) -
            (outerWeight t : ℝ)) := by
    field_simp
    ring

  rw [hIdentity]

  calc
    |((GoodCoreQuotientCount N t : ℝ) -
          (4 / 15 : ℝ) *
            (QuotientIntervalLength N t : ℝ)) /
          (N : ℝ) +
        (4 / 15 : ℝ) *
          ((QuotientIntervalLength N t : ℝ) /
              (N : ℝ) -
            (outerWeight t : ℝ))|
        ≤
      |((GoodCoreQuotientCount N t : ℝ) -
          (4 / 15 : ℝ) *
            (QuotientIntervalLength N t : ℝ)) /
          (N : ℝ)| +
        |(4 / 15 : ℝ) *
          ((QuotientIntervalLength N t : ℝ) /
              (N : ℝ) -
            (outerWeight t : ℝ))| :=
      abs_add _ _

    _ ≤
      16 / (N : ℝ) +
        (4 / 15 : ℝ) *
          (2 / (N : ℝ)) := by
      exact add_le_add
        hCountErrorNormalized
        hFloorErrorScaled

    _ ≤ 17 / (N : ℝ) := by
      have hNumeric :
          (16 : ℝ) + (4 / 15) * 2 ≤ 17 := by
        norm_num

      have hInvNonneg :
          0 ≤ (1 / (N : ℝ)) := by
        positivity

      calc
        16 / (N : ℝ) +
            (4 / 15 : ℝ) *
              (2 / (N : ℝ))
            =
          ((16 : ℝ) + (4 / 15) * 2) *
            (1 / (N : ℝ)) := by
              ring

        _ ≤
          17 * (1 / (N : ℝ)) :=
            mul_le_mul_of_nonneg_right
              hNumeric hInvNonneg

        _ = 17 / (N : ℝ) := by
          ring

end Erdos536813
