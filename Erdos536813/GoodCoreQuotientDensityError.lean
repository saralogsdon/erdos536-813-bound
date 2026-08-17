import Erdos536813.GoodCoreQuotientCountDifference

namespace Erdos536813

/--
Each positive quotient-fiber count differs by at most `16` from density
`4/15` times the length of its quotient interval.
-/
theorem goodCoreQuotientCount_density_error
    {N t : Nat}
    (htPos : 0 < t) :
    |(GoodCoreQuotientCount N t : ℝ) -
        (4 / 15 : ℝ) *
          ((N / t : Nat) -
            (N / (t + 1) : Nat))| ≤ 16 := by

  have hSubset :=
    goodCoreFinset_div_succ_subset_div
      (N := N) htPos

  have hCountLe :
      GoodCoreCount (N / (t + 1)) ≤
        GoodCoreCount (N / t) := by
    unfold GoodCoreCount
    exact Finset.card_le_card hSubset

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
      |(GoodCoreCount (N / t) : ℝ) -
          (4 / 15 : ℝ) * (N / t : Nat)| ≤ 8 :=
    goodCoreCount_sub_density_bound
      (N / t)

  have hLowerError :
      |(GoodCoreCount (N / (t + 1)) : ℝ) -
          (4 / 15 : ℝ) *
            (N / (t + 1) : Nat)| ≤ 8 :=
    goodCoreCount_sub_density_bound
      (N / (t + 1))

  rw [goodCoreQuotientCount_eq_count_sub htPos]
  rw [Nat.cast_sub hCountLe]
  rw [Nat.cast_sub hDivLe]

  have hIdentity :
      (GoodCoreCount (N / t) : ℝ) -
          (GoodCoreCount (N / (t + 1)) : ℝ) -
          (4 / 15 : ℝ) *
            ((N / t : ℝ) -
              (N / (t + 1) : ℝ))
        =
      ((GoodCoreCount (N / t) : ℝ) -
          (4 / 15 : ℝ) * (N / t : ℝ)) -
        ((GoodCoreCount (N / (t + 1)) : ℝ) -
          (4 / 15 : ℝ) *
            (N / (t + 1) : ℝ)) := by
    ring

  rw [hIdentity]

  calc
    |((GoodCoreCount (N / t) : ℝ) -
          (4 / 15 : ℝ) * (N / t : ℝ)) -
        ((GoodCoreCount (N / (t + 1)) : ℝ) -
          (4 / 15 : ℝ) *
            (N / (t + 1) : ℝ))|
        ≤
      |(GoodCoreCount (N / t) : ℝ) -
          (4 / 15 : ℝ) * (N / t : ℝ)| +
        |(GoodCoreCount (N / (t + 1)) : ℝ) -
          (4 / 15 : ℝ) *
            (N / (t + 1) : ℝ)| :=
      abs_sub _ _

    _ ≤ 16 := by
      linarith

end Erdos536813
