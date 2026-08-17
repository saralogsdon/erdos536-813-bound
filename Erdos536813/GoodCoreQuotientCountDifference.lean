import Erdos536813.GlobalTargetQuotientReindex

namespace Erdos536813

/--
For positive `t`, the equation `N / m = t` is equivalent to the usual
quotient interval condition
`N/(t+1) < m ≤ N/t`.
-/
theorem nat_div_eq_iff_interval
    {N m t : Nat}
    (hmPos : 0 < m)
    (htPos : 0 < t) :
    N / m = t ↔
      N / (t + 1) < m ∧
        m ≤ N / t := by

  constructor
  · intro hEq

    have hMulUpper :
        m * t ≤ N := by
      have h :=
        Nat.div_mul_le_self N m
      rw [hEq] at h
      simpa [Nat.mul_comm] using h

    have hmUpper :
        m ≤ N / t :=
      (Nat.le_div_iff_mul_le htPos).mpr
        hMulUpper

    have hmLower :
        N / (t + 1) < m := by
      by_contra hNot

      have hmLe :
          m ≤ N / (t + 1) := by
        omega

      have hMulLower :
          m * (t + 1) ≤ N :=
        (Nat.le_div_iff_mul_le
          (Nat.succ_pos t)).mp hmLe

      have hQuotientLower :
          t + 1 ≤ N / m := by
        apply
          (Nat.le_div_iff_mul_le hmPos).mpr
        simpa [Nat.mul_comm] using hMulLower

      rw [hEq] at hQuotientLower
      omega

    exact ⟨hmLower, hmUpper⟩

  · intro hInterval

    have hMulLower :
        m * t ≤ N :=
      (Nat.le_div_iff_mul_le htPos).mp
        hInterval.2

    have hQuotientLower :
        t ≤ N / m := by
      apply
        (Nat.le_div_iff_mul_le hmPos).mpr
      simpa [Nat.mul_comm] using hMulLower

    have hMulUpper :
        N < m * (t + 1) :=
      (Nat.div_lt_iff_lt_mul
        (Nat.succ_pos t)).mp
        hInterval.1

    have hQuotientUpper :
        N / m < t + 1 := by
      apply
        (Nat.div_lt_iff_lt_mul hmPos).mpr
      simpa [Nat.mul_comm] using hMulUpper

    omega

/--
For positive `t`, the quotient fiber is exactly the difference between the
good-core finsets at its upper and lower endpoints.
-/
theorem goodCoreQuotientFinset_eq_sdiff
    {N t : Nat}
    (htPos : 0 < t) :
    GoodCoreQuotientFinset N t =
      GoodCoreFinset (N / t) \
        GoodCoreFinset (N / (t + 1)) := by

  classical

  ext m

  constructor
  · intro hm

    have hmData :=
      mem_goodCoreQuotientFinset_iff.mp hm

    have hInterval :=
      (nat_div_eq_iff_interval
        hmData.2.1.1 htPos).mp
        hmData.2.2

    apply Finset.mem_sdiff.mpr

    constructor
    · apply mem_goodCoreFinset_iff.mpr
      exact
        ⟨hInterval.2,
          hmData.2.1⟩

    · intro hmLower

      have hmLowerData :=
        mem_goodCoreFinset_iff.mp hmLower

      omega

  · intro hm

    have hmData :=
      Finset.mem_sdiff.mp hm

    have hmUpper :=
      mem_goodCoreFinset_iff.mp hmData.1

    have hmLower :
        N / (t + 1) < m := by
      by_contra hNot

      have hmLe :
          m ≤ N / (t + 1) := by
        omega

      apply hmData.2

      exact
        mem_goodCoreFinset_iff.mpr
          ⟨hmLe, hmUpper.2⟩

    have hEq :
        N / m = t :=
      (nat_div_eq_iff_interval
        hmUpper.2.1 htPos).mpr
        ⟨hmLower, hmUpper.1⟩

    apply mem_goodCoreQuotientFinset_iff.mpr

    have hmLeN :
        m ≤ N := by
      exact Nat.le_trans
        hmUpper.1
        (Nat.div_le_self N t)

    exact
      ⟨hmLeN, hmUpper.2, hEq⟩

/--
The lower-endpoint good-core finset is contained in the upper-endpoint
finset.
-/
theorem goodCoreFinset_div_succ_subset_div
    {N t : Nat}
    (htPos : 0 < t) :
    GoodCoreFinset (N / (t + 1)) ⊆
      GoodCoreFinset (N / t) := by

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

  intro m hm

  have hmData :=
    mem_goodCoreFinset_iff.mp hm

  exact
    mem_goodCoreFinset_iff.mpr
      ⟨Nat.le_trans hmData.1 hDivLe,
        hmData.2⟩

/--
Thus each positive quotient-fiber count is the difference of the good-core
counting function at the two quotient endpoints.
-/
theorem goodCoreQuotientCount_eq_count_sub
    {N t : Nat}
    (htPos : 0 < t) :
    GoodCoreQuotientCount N t =
      GoodCoreCount (N / t) -
        GoodCoreCount (N / (t + 1)) := by

  unfold GoodCoreQuotientCount
    GoodCoreCount

  rw [goodCoreQuotientFinset_eq_sdiff htPos]

  exact
    Finset.card_sdiff
      (goodCoreFinset_div_succ_subset_div htPos)

end Erdos536813
