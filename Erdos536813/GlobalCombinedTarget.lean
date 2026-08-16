import Erdos536813.CanonicalHighDepth

namespace Erdos536813

/--
The target saving attached to a normalized core scale.

For scales below `120`, use the finite deficit table. For high scales,
use the canonical high-depth target.
-/
noncomputable def CombinedCoreTarget
    (t : Nat) : Nat :=
  if 120 ≤ t then
    highFiberTarget
      (CanonicalHighDepth t)
      (FiveScale t (CanonicalHighDepth t))
  else
    finiteTargetDeficit t

/--
The canonical high target subtracts from the complete chain of a core.
-/
theorem canonicalHighTarget_plus_coreIntegerSum_le_baseline
    {A : List Nat}
    {N m : Nat}
    (hm : GoodThirtyCore m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (ht : 120 ≤ N / m) :
    highFiberTarget
          (CanonicalHighDepth (N / m))
          (FiveScale
            (N / m)
            (CanonicalHighDepth (N / m))) +
        CoreIntegerSum A N m
      ≤ CoreBaselineSum N m := by

  have hSpec :=
    canonicalHighDepth_spec ht

  have hFinal :
      1 ≤
        FiveScale
          (N / m)
          (highSafeDepth
            (CanonicalHighDepth (N / m))
            (FiveScale
              (N / m)
              (CanonicalHighDepth (N / m)))) :=
    fiveScale_highSafeDepth_pos
      hSpec.2.1
      hSpec.2.2.1

  have hSub :
      Finset.range
          (highSafeDepth
            (CanonicalHighDepth (N / m))
            (FiveScale
              (N / m)
              (CanonicalHighDepth (N / m))) + 1)
        ⊆ CoreDepthFinset N m :=
    range_subset_coreDepthFinset_of_final_scale_pos
      hm hFinal

  have hTarget :
      highFiberTarget
          (CanonicalHighDepth (N / m))
          (FiveScale
            (N / m)
            (CanonicalHighDepth (N / m)))
        ≤
      PrefixDeficit
        (FiberSliceDeficit
          (N / m)
          (ActualFiveSlice A N m))
        (highSafeDepth
          (CanonicalHighDepth (N / m))
          (FiveScale
            (N / m)
            (CanonicalHighDepth (N / m)))) :=
    highTarget_le_actualFiveFiber_safe
      hm.1 hA hSpec.2.2.2

  exact
    target_plus_coreIntegerSum_le_baseline_of_prefix
      (A := A)
      (N := N)
      (m := m)
      (r :=
        highSafeDepth
          (CanonicalHighDepth (N / m))
          (FiveScale
            (N / m)
            (CanonicalHighDepth (N / m))))
      (target :=
        highFiberTarget
          (CanonicalHighDepth (N / m))
          (FiveScale
            (N / m)
            (CanonicalHighDepth (N / m))))
      hm hA hSub hTarget

/--
The combined finite/high target subtracts from every complete core chain.
-/
theorem combinedCoreTarget_plus_coreIntegerSum_le_baseline
    {A : List Nat}
    {N m : Nat}
    (hm : GoodThirtyCore m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    CombinedCoreTarget (N / m) +
        CoreIntegerSum A N m
      ≤ CoreBaselineSum N m := by

  by_cases ht : 120 ≤ N / m

  · simpa [CombinedCoreTarget, ht] using
      canonicalHighTarget_plus_coreIntegerSum_le_baseline
        hm hA ht

  · simpa [CombinedCoreTarget, ht] using
      finiteTarget_plus_coreIntegerSum_le_baseline
        hm hA

/-- Total combined target saving over all admissible cores. -/
noncomputable def GlobalCombinedTargetSum
    (N : Nat) : Nat :=
  ∑ m ∈ GoodCoreFinset N,
    CombinedCoreTarget (N / m)

/--
Summing the combined target over every core gives the full global saving.
-/
theorem globalCombinedTarget_add_globalCoreIntegerSum_le_baseline
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    GlobalCombinedTargetSum N +
        GlobalCoreIntegerSum A N
      ≤ GlobalCoreBaselineSum N := by

  unfold GlobalCombinedTargetSum
    GlobalCoreIntegerSum
    GlobalCoreBaselineSum

  rw [← Finset.sum_add_distrib]

  apply Finset.sum_le_sum
  intro m hm

  exact
    combinedCoreTarget_plus_coreIntegerSum_le_baseline
      ((mem_goodCoreFinset_iff.mp hm).2)
      hA

/--
The original cardinality plus the full finite/high target saving is
bounded by the global baseline.
-/
theorem card_add_globalCombinedTarget_le_globalCoreBaseline
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    A.length + GlobalCombinedTargetSum N
      ≤ GlobalCoreBaselineSum N := by

  have hCard :=
    card_le_globalCoreIntegerSum hA

  have hSaving :=
    globalCombinedTarget_add_globalCoreIntegerSum_le_baseline hA

  omega

end Erdos536813
