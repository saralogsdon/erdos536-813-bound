import Erdos536813.SafeHighFiberPrefix

namespace Erdos536813

/-!
# Exact characterization of the finite factor-5 code list

The previous regrouping theorem showed that every code occurring in
`GoodBaseFiveCodeList N` has a positive core coprime to `30` and reconstructs
a good base at most `N`.

Here we prove the converse: every pair `(m,k)` with `m` a good `30`-core and
`m * 5^k ≤ N` occurs in that code list.  Thus the reindexed global sum is
exactly the finite union of complete 5-adic chains.
-/

/-- Every power of `5` is coprime to `6`. -/
theorem five_pow_coprime_six
    (k : Nat) :
    Nat.Coprime (5 ^ k) 6 := by
  have h56 : Nat.Coprime 5 6 := by
    norm_num
  exact h56.pow_left k

/-- A positive core coprime to `30` generates a good upstream fiber base at every depth. -/
theorem fiveBase_goodFiberBase
    {m k : Nat}
    (hm : GoodThirtyCore m) :
    Erdos536.GoodFiberBase (FiveBase m k) := by

  have hm6 :
      Nat.Coprime m 6 :=
    hm.2.coprime_dvd_right
      (by norm_num : 6 ∣ 30)

  have h5k6 :
      Nat.Coprime (5 ^ k) 6 :=
    five_pow_coprime_six k

  have hprod :
      Nat.Coprime (m * 5 ^ k) 6 :=
    Nat.Coprime.mul_left hm6 h5k6

  refine ⟨?_, ?_⟩
  · unfold FiveBase
    exact Nat.mul_pos hm.1
      (Nat.pow_pos (by norm_num : 0 < (5 : Nat)))
  · simpa [FiveBase] using hprod

/-- The canonical code of `m * 5^k` is exactly `(m,k)` for a good `30`-core. -/
theorem fiveCode_fiveBase
    {m k : Nat}
    (hm : GoodThirtyCore m) :
    FiveCode (FiveBase m k) = (m, k) := by

  have hqPos :
      0 < FiveBase m k := by
    unfold FiveBase
    exact Nat.mul_pos hm.1
      (Nat.pow_pos (by norm_num : 0 < (5 : Nat)))

  have hUnique :=
    five_decomposition_unique
      (q := FiveBase m k)
      (m := m)
      (k := k)
      hqPos hm
      (by rfl)

  unfold FiveCode
  apply Prod.ext
  · exact hUnique.1.symm
  · exact hUnique.2.symm

/--
Exact membership in the finite reindexing list:

`(m,k)` occurs iff `m` is a positive core coprime to `30` and the actual
base `m * 5^k` is at most `N`.
-/
theorem mem_goodBaseFiveCodeList_iff
    {N m k : Nat} :
    (m, k) ∈ GoodBaseFiveCodeList N ↔
      GoodThirtyCore m ∧ FiveBase m k ≤ N := by

  constructor
  · intro h
    have hData :=
      mem_goodBaseFiveCodeList_data h
    exact ⟨hData.1, hData.2.1⟩

  · rintro ⟨hm, hBound⟩

    have hGood :
        Erdos536.GoodFiberBase (FiveBase m k) :=
      fiveBase_goodFiberBase hm

    have hBaseMem :
        FiveBase m k ∈ GoodBaseUpToList N :=
      mem_goodBaseUpToList.mpr ⟨hBound, hGood⟩

    unfold GoodBaseFiveCodeList
    rw [List.mem_map]
    refine ⟨FiveBase m k, hBaseMem, ?_⟩
    exact fiveCode_fiveBase hm

/--
A useful uniqueness formulation: inside the finite code list, a reconstructed
base determines its core and depth uniquely.
-/
theorem goodBaseFiveCode_eq_of_same_base
    {N m k m' k' : Nat}
    (h : (m, k) ∈ GoodBaseFiveCodeList N)
    (h' : (m', k') ∈ GoodBaseFiveCodeList N)
    (hEq : FiveBase m k = FiveBase m' k') :
    m = m' ∧ k = k' := by

  have hm := (mem_goodBaseFiveCodeList_iff.mp h).1
  have hm' := (mem_goodBaseFiveCodeList_iff.mp h').1

  have hqPos :
      0 < FiveBase m k :=
    (fiveBase_goodFiberBase hm).1

  exact
    goodThirty_five_decomposition_injective
      (q := FiveBase m k)
      (m := m) (k := k)
      (m' := m') (k' := k')
      hqPos hm hm'
      rfl hEq

end Erdos536813
