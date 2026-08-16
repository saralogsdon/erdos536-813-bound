import Erdos536813.CompleteFiveChain

namespace Erdos536813

noncomputable def GoodCoreFinset (N : Nat) : Finset Nat :=
  (Finset.range (N + 1)).filter (fun m => decide (GoodThirtyCore m))

theorem mem_goodCoreFinset_iff
    {N m : Nat} :
    m ∈ GoodCoreFinset N ↔
      m ≤ N ∧ GoodThirtyCore m := by
  classical
  unfold GoodCoreFinset
  simp
  constructor
  · intro h
    exact ⟨h.1, of_decide_eq_true h.2⟩
  · rintro ⟨hmN, hm⟩
    exact ⟨hmN, decide_eq_true_eq.mpr hm⟩

theorem globalCode_mem_some_core
    {N m k : Nat}
    (hCode :
      (m, k) ∈ GoodBaseFiveCodeList N) :
    m ∈ GoodCoreFinset N ∧
      k ∈ CoreDepthFinset N m := by
  have hData :
      GoodThirtyCore m ∧ FiveBase m k ≤ N :=
    mem_goodBaseFiveCodeList_iff.mp hCode
  constructor
  · apply mem_goodCoreFinset_iff.mpr
    have hmle :
        m ≤ FiveBase m k := by
      unfold FiveBase
      have hmpos : 0 < m := hData.1.1
      have hpow : 1 ≤ 5 ^ k := by positivity
      omega
    exact ⟨le_trans hmle hData.2, hData.1⟩
  · exact
      (mem_coreDepthFinset_iff_global_code hData.1).mpr hCode

theorem coreDepth_mem_globalCode
    {N m k : Nat}
    (hm : GoodThirtyCore m)
    (hk : k ∈ CoreDepthFinset N m) :
    (m, k) ∈ GoodBaseFiveCodeList N := by
  exact
    (mem_coreDepthFinset_iff_global_code hm).mp hk

theorem globalCode_toFinset_eq_biUnion_coreDepth
    {N : Nat} :
    (GoodBaseFiveCodeList N).toFinset =
      (GoodCoreFinset N).biUnion
        (fun m =>
          (CoreDepthFinset N m).image
            (fun k => (m, k))) := by
  classical
  ext p
  constructor
  · intro hp
    have hpList :
        p ∈ GoodBaseFiveCodeList N :=
      List.mem_toFinset.mp hp
    rcases p with ⟨m, k⟩
    have hCore :
        m ∈ GoodCoreFinset N ∧
          k ∈ CoreDepthFinset N m :=
      globalCode_mem_some_core hpList
    apply Finset.mem_biUnion.mpr
    refine ⟨m, hCore.1, ?_⟩
    exact Finset.mem_image.mpr
      ⟨k, hCore.2, rfl⟩
  · intro hp
    rcases Finset.mem_biUnion.mp hp with
      ⟨m, hm, hp⟩
    rcases Finset.mem_image.mp hp with
      ⟨k, hk, rfl⟩
    apply List.mem_toFinset.mpr
    exact coreDepth_mem_globalCode
      ((mem_goodCoreFinset_iff.mp hm).2)
      hk

end Erdos536813
