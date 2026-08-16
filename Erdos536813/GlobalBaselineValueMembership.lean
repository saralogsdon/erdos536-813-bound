import Erdos536813.GlobalBaselineValues

namespace Erdos536813

/--
Every point in the explicit axis benchmark is an axis point whose ordinary
fiber value is at most the benchmark scale.
-/
theorem axisBenchmarkList_mem_data
    {T : Nat}
    {p : Erdos536.GridPoint}
    (hT : T ≠ 0)
    (hp : p ∈ AxisBenchmarkList T) :
    Erdos536.GridPoint.axis p ∧
      Erdos536.fiberValue 1 p ≤ T := by

  rw [AxisBenchmarkList, List.mem_append] at hp
  rcases hp with hp | hp

  · rw [List.mem_map] at hp
    rcases hp with ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi

    have hile :
        i ≤ Nat.log 2 T := by
      omega

    have hPow :
        2 ^ i ≤ T := by
      exact Nat.le_trans
        (Nat.pow_le_pow_right
          (by decide : 0 < (2 : Nat)) hile)
        (Nat.pow_log_le_self 2 hT)

    constructor
    · simp [Erdos536.GridPoint.axis]
    · simpa [Erdos536.fiberValue] using hPow

  · rw [List.mem_map] at hp
    rcases hp with ⟨j, hj, rfl⟩
    rw [List.mem_range] at hj

    have hjle :
        j + 1 ≤ Nat.log 3 T := by
      omega

    have hPow :
        3 ^ (j + 1) ≤ T := by
      exact Nat.le_trans
        (Nat.pow_le_pow_right
          (by decide : 0 < (3 : Nat)) hjle)
        (Nat.pow_log_le_self 3 hT)

    constructor
    · simp [Erdos536.GridPoint.axis]
    · simpa [Erdos536.fiberValue] using hPow

/--
The value represented by every global baseline pair is a positive integer at
most `N` and is not divisible by six.
-/
theorem globalBaselinePairValue_mem_nonSixUpToList
    {N : Nat}
    {qp : Nat × Erdos536.GridPoint}
    (hqp : qp ∈ GlobalBaselinePairs N) :
    GlobalBaselinePairValue qp ∈
      Erdos536.NonSixUpToList N := by

  have hPairData := mem_globalBaselinePairs.mp hqp
  have hBaseData :=
    mem_goodBaseUpToList.mp hPairData.1

  have hqLe : qp.1 ≤ N :=
    hBaseData.1

  have hqGood : Erdos536.GoodFiberBase qp.1 :=
    hBaseData.2

  have hScalePos : 0 < N / qp.1 :=
    Nat.div_pos hqLe hqGood.1

  have hpData :=
    axisBenchmarkList_mem_data
      hScalePos.ne'
      hPairData.2

  have hpAxis :
      Erdos536.GridPoint.axis qp.2 :=
    hpData.1

  have hpBound :
      Erdos536.fiberValue 1 qp.2 ≤ N / qp.1 :=
    hpData.2

  have hValueEq :
      GlobalBaselinePairValue qp =
        qp.1 * Erdos536.fiberValue 1 qp.2 := by
    simp [
      GlobalBaselinePairValue,
      Erdos536.fiberValue,
      Nat.mul_assoc
    ]

  have hValueLe :
      GlobalBaselinePairValue qp ≤ N := by
    rw [hValueEq]
    calc
      qp.1 * Erdos536.fiberValue 1 qp.2
          ≤ qp.1 * (N / qp.1) :=
        Nat.mul_le_mul_left qp.1 hpBound
      _ = (N / qp.1) * qp.1 := by
        rw [Nat.mul_comm]
      _ ≤ N :=
        Nat.div_mul_le_self N qp.1

  have hValuePos :
      0 < GlobalBaselinePairValue qp := by
    unfold GlobalBaselinePairValue
    exact Erdos536.fiberValue_pos hqGood.1 qp.2

  have hNotSix :
      ¬ 6 ∣ GlobalBaselinePairValue qp := by
    unfold GlobalBaselinePairValue
    exact
      Erdos536.not_six_dvd_fiberValue_of_axis_coprime
        hqGood.2 hpAxis

  have hRange :
      GlobalBaselinePairValue qp ∈
        List.range (N + 1) := by
    rw [List.mem_range]
    exact Nat.lt_succ_of_le hValueLe

  simp [
    Erdos536.NonSixUpToList,
    hRange,
    hValuePos,
    hValueLe,
    hNotSix
  ]

/--
The entire global baseline value list is contained in the upstream list of
positive integers at most `N` that are not divisible by six.
-/
theorem globalBaselineValueList_subset_nonSixUpToList
    {N : Nat} :
    (GlobalBaselineValueList N).Subset
      (Erdos536.NonSixUpToList N) := by

  intro n hn
  rw [GlobalBaselineValueList, List.mem_map] at hn
  rcases hn with ⟨qp, hqp, rfl⟩
  exact globalBaselinePairValue_mem_nonSixUpToList hqp

end Erdos536813
