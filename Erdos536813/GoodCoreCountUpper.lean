import Erdos536813.GoodCoreCountLower

namespace Erdos536813

/--
Every good core at most `30*b` occurs in the concatenation of the first
`b` complete residue blocks.
-/
theorem goodCoreFinset_subset_initialBlockList
    {b m : Nat}
    (hm : m ∈ GoodCoreFinset (30 * b)) :
    m ∈ GoodCoreInitialBlockList b := by

  have hmData :=
    mem_goodCoreFinset_iff.mp hm

  have hmLe :
      m ≤ 30 * b :=
    hmData.1

  have hmGood :
      GoodThirtyCore m :=
    hmData.2

  have hmPos :
      0 < m :=
    hmGood.1

  let j : Nat :=
    (m - 1) / 30

  have hjLt :
      j < b := by
    have hmPredLt :
        m - 1 < 30 * b := by
      omega

    dsimp [j]

    exact
      (Nat.div_lt_iff_lt_mul
        (by norm_num : 0 < (30 : Nat))).mpr
        hmPredLt

  have hDecomp :
      (m - 1) % 30 +
          30 * ((m - 1) / 30)
        =
      m - 1 :=
    Nat.mod_add_div (m - 1) 30

  have hMod :
      (m - 1) % 30 < 30 :=
    Nat.mod_lt (m - 1)
      (by norm_num : 0 < (30 : Nat))

  have hLower :
      30 * j < m := by
    dsimp [j]
    omega

  have hUpperWeak :
      m ≤ 30 * (j + 1) := by
    dsimp [j]
    omega

  have hNotDiv :
      ¬ 30 ∣ m := by
    intro hDiv

    have hEq :
        30 = 1 :=
      hmGood.2.symm.eq_one_of_dvd hDiv

    norm_num at hEq

  have hUpper :
      m < 30 * (j + 1) := by
    by_contra hNot
    have hEq :
        m = 30 * (j + 1) := by
      omega

    apply hNotDiv

    rw [hEq]

    exact Nat.dvd_mul_right 30 (j + 1)

  rw [GoodCoreInitialBlockList, List.mem_flatMap]

  refine
    ⟨j, List.mem_range.mpr hjLt, ?_⟩

  exact
    goodCore_mem_residueBlockList
      hLower hUpper hmGood

/--
At a complete cutoff `30*b`, the good-core count is exactly `8*b`.
-/
theorem goodCoreCount_thirty_mul
    (b : Nat) :
    GoodCoreCount (30 * b) = 8 * b := by

  apply Nat.le_antisymm

  · unfold GoodCoreCount

    have hSubset :
        GoodCoreFinset (30 * b) ⊆
          (GoodCoreInitialBlockList b).toFinset := by
      intro m hm

      have hmList :
          m ∈ GoodCoreInitialBlockList b :=
        goodCoreFinset_subset_initialBlockList hm

      simpa using hmList

    calc
      (GoodCoreFinset (30 * b)).card
          ≤
        (GoodCoreInitialBlockList b).toFinset.card :=
          Finset.card_le_card hSubset

      _ =
        (GoodCoreInitialBlockList b).length := by
          exact
            List.toFinset_card_of_nodup
              (goodCoreInitialBlockList_nodup b)

      _ = 8 * b :=
        goodCoreInitialBlockList_length b

  · exact
      eight_mul_le_goodCoreFinset_card b

/--
For arbitrary `X`, at most one additional incomplete block occurs.
-/
theorem goodCoreCount_le_eight_mul_succ_div
    (X : Nat) :
    GoodCoreCount X ≤
      8 * (X / 30 + 1) := by

  have hCutoff :
      X ≤ 30 * (X / 30 + 1) := by

    have hDecomp :
        X % 30 + 30 * (X / 30) = X :=
      Nat.mod_add_div X 30

    have hMod :
        X % 30 < 30 :=
      Nat.mod_lt X
        (by norm_num : 0 < (30 : Nat))

    omega

  calc
    GoodCoreCount X
        ≤
      GoodCoreCount (30 * (X / 30 + 1)) :=
        goodCoreCount_mono hCutoff

    _ =
      8 * (X / 30 + 1) :=
        goodCoreCount_thirty_mul
          (X / 30 + 1)

/--
A denominator-free upper density estimate with a uniform error.
-/
theorem fifteen_mul_goodCoreCount_le_four_mul_add
    (X : Nat) :
    15 * GoodCoreCount X ≤
      4 * X + 120 := by

  have hUpper :=
    goodCoreCount_le_eight_mul_succ_div X

  have hDivMul :
      30 * (X / 30) ≤ X :=
    Nat.mul_div_le X 30

  omega

end Erdos536813
