import Erdos536813.TargetPrefixGlobal

namespace Erdos536813

theorem succ_le_pow_five (k : Nat) : k + 1 ≤ 5 ^ k := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      rw [Nat.pow_succ]
      omega

theorem depth_le_of_fiveBase_le
    {N m k : Nat}
    (hm : GoodThirtyCore m)
    (hBase : FiveBase m k ≤ N) :
    k ≤ N := by
  have hmPos : 0 < m := hm.1
  have hmOne : 1 ≤ m := by omega
  have hPowBase : 5 ^ k ≤ FiveBase m k := by
    unfold FiveBase
    have h := Nat.mul_le_mul_right (5 ^ k) hmOne
    simpa using h
  have hGrow : k + 1 ≤ 5 ^ k := succ_le_pow_five k
  omega

def CoreDepthFinset (N m : Nat) : Finset Nat :=
  (Finset.range (N + 1)).filter (fun k => FiveBase m k ≤ N)

theorem mem_coreDepthFinset_iff
    {N m k : Nat}
    (hm : GoodThirtyCore m) :
    k ∈ CoreDepthFinset N m ↔ FiveBase m k ≤ N := by
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hBase
    have hkN : k ≤ N := depth_le_of_fiveBase_le hm hBase
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hkN), hBase⟩

theorem mem_coreDepthFinset_iff_global_code
    {N m k : Nat}
    (hm : GoodThirtyCore m) :
    k ∈ CoreDepthFinset N m ↔
      (m, k) ∈ GoodBaseFiveCodeList N := by
  rw [mem_coreDepthFinset_iff hm]
  rw [mem_goodBaseFiveCodeList_iff]
  simp [hm]

theorem range_subset_coreDepthFinset_of_final_scale_pos
    {N m r : Nat}
    (hm : GoodThirtyCore m)
    (hFinal : 1 ≤ FiveScale (N / m) r) :
    Finset.range (r + 1) ⊆ CoreDepthFinset N m := by
  intro k hk
  have hkLe : k ≤ r := by
    have hkLt : k < r + 1 := Finset.mem_range.mp hk
    omega
  have hGlobal :
      (m, k) ∈ GoodBaseFiveCodeList N :=
    fivePrefix_mem_global_of_final_scale_pos hm hFinal k hkLe
  exact (mem_coreDepthFinset_iff_global_code hm).mpr hGlobal

theorem finiteTarget_range_subset_coreDepthFinset
    {N m : Nat}
    (hm : GoodThirtyCore m)
    (hTarget : 0 < finiteTargetDeficit (N / m)) :
    Finset.range 2 ⊆ CoreDepthFinset N m := by
  have hFinal :
      1 ≤ FiveScale (N / m) 1 :=
    finiteTargetDeficit_pos_implies_scale_one_pos hTarget
  simpa using
    (range_subset_coreDepthFinset_of_final_scale_pos
      (N := N) (m := m) (r := 1) hm hFinal)

theorem exists_canonical_safe_highTarget_coreDepth_subset
    {A : List Nat}
    {N m : Nat}
    (hm : GoodThirtyCore m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (ht : 120 ≤ N / m) :
    ∃ n : Nat,
      1 ≤ n ∧
      24 ≤ FiveScale (N / m) n ∧
      FiveScale (N / m) n ≤ 119 ∧
      1 ≤ FiveScale (N / m)
        (highSafeDepth n (FiveScale (N / m) n)) ∧
      Finset.range
          (highSafeDepth n (FiveScale (N / m) n) + 1)
        ⊆ CoreDepthFinset N m ∧
      highFiberTarget n (FiveScale (N / m) n) +
          ActualFiveIntegerPrefix A N m
            (highSafeDepth n (FiveScale (N / m) n)) ≤
        FiveBaselinePrefix N m
          (highSafeDepth n (FiveScale (N / m) n)) := by
  rcases
    exists_canonical_safe_highTarget_bound
      (A := A) (N := N) (m := m)
      hm.1 hA ht
    with ⟨n, hn, hLower, hUpper, hFinal, hBound⟩
  have hSubset :
      Finset.range
          (highSafeDepth n (FiveScale (N / m) n) + 1)
        ⊆ CoreDepthFinset N m :=
    range_subset_coreDepthFinset_of_final_scale_pos hm hFinal
  exact ⟨n, hn, hLower, hUpper, hFinal, hSubset, hBound⟩

noncomputable def CoreIntegerSum
    (A : List Nat) (N m : Nat) : Nat :=
  ∑ k ∈ CoreDepthFinset N m,
    (Erdos536.FiberIntegerList A (FiveBase m k)).length

def CoreBaselineSum
    (N m : Nat) : Nat :=
  ∑ k ∈ CoreDepthFinset N m,
    L23 (FiveScale (N / m) k)

end Erdos536813
