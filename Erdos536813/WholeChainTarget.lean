import Erdos536813.CompleteFiveChain

namespace Erdos536813

/-!
# Extending target savings to complete 5-adic chains

For a fixed positive core coprime to `30`, the preceding file packages every
actual depth `k` with `m * 5^k ≤ N` into `CoreDepthFinset N m`.

The verified finite/high target only uses an initial prefix of this chain.
Because slice deficits are nonnegative, the deficit sum over that prefix is
at most the deficit sum over the complete chain. Summing the pointwise
benchmark

    FiberIntegerList + slice deficit ≤ L23

over the complete chain then gives the desired whole-chain target saving.
-/

/-- Total actual slice deficit over the complete finite chain of a core. -/
def CoreDeficitSum
    (A : List Nat)
    (N m : Nat) : Nat :=
  ∑ k ∈ CoreDepthFinset N m,
    FiberSliceDeficit
      (N / m)
      (ActualFiveSlice A N m)
      k

/--
Any deficit prefix contained in the complete core depth set has no more
deficit than the whole chain.
-/
theorem prefixDeficit_le_coreDeficitSum
    {A : List Nat}
    {N m r : Nat}
    (hSub :
      Finset.range (r + 1) ⊆
        CoreDepthFinset N m) :
    PrefixDeficit
        (FiberSliceDeficit
          (N / m)
          (ActualFiveSlice A N m))
        r
      ≤ CoreDeficitSum A N m := by

  unfold PrefixDeficit CoreDeficitSum

  apply Finset.sum_le_sum_of_subset_of_nonneg hSub
  intro k hk hNot
  exact Nat.zero_le _

/--
Pointwise upstream fiber count plus the actual verified deficit is bounded
by the corresponding `L23` benchmark.
-/
theorem coreLayer_integer_add_deficit_le_baseline
    {A : List Nat}
    {N m k : Nat}
    (hm : GoodThirtyCore m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    (Erdos536.FiberIntegerList A (FiveBase m k)).length +
        FiberSliceDeficit
          (N / m)
          (ActualFiveSlice A N m)
          k
      ≤ L23 (FiveScale (N / m) k) := by

  exact
    fiberIntegerList_add_actual_deficit_le_L23
      (A := A) (N := N) (m := m) (k := k)
      hm.1 hA

/--
Summing the preceding pointwise inequality over every actual depth of a core
gives the complete-chain benchmark with its complete deficit.
-/
theorem coreIntegerSum_add_coreDeficit_le_baseline
    {A : List Nat}
    {N m : Nat}
    (hm : GoodThirtyCore m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    CoreIntegerSum A N m +
        CoreDeficitSum A N m
      ≤ CoreBaselineSum N m := by

  unfold CoreIntegerSum CoreDeficitSum CoreBaselineSum

  rw [← Finset.sum_add_distrib]

  apply Finset.sum_le_sum
  intro k hk

  exact
    coreLayer_integer_add_deficit_le_baseline
      (A := A) (N := N) (m := m) (k := k)
      hm hA

/--
Generic extension principle: if a target is paid for by the deficit on an
initial prefix, and that prefix lies in the complete chain, then the same
target subtracts from the whole-chain integer-fiber total.
-/
theorem target_plus_coreIntegerSum_le_baseline_of_prefix
    {A : List Nat}
    {N m r target : Nat}
    (hm : GoodThirtyCore m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hSub :
      Finset.range (r + 1) ⊆
        CoreDepthFinset N m)
    (hTarget :
      target ≤
        PrefixDeficit
          (FiberSliceDeficit
            (N / m)
            (ActualFiveSlice A N m))
          r) :
    target + CoreIntegerSum A N m
      ≤ CoreBaselineSum N m := by

  have hPrefixWhole :
      PrefixDeficit
          (FiberSliceDeficit
            (N / m)
            (ActualFiveSlice A N m))
          r
        ≤ CoreDeficitSum A N m :=
    prefixDeficit_le_coreDeficitSum
      (A := A) (N := N) (m := m) (r := r)
      hSub

  have hTargetWhole :
      target ≤ CoreDeficitSum A N m :=
    hTarget.trans hPrefixWhole

  have hWhole :=
    coreIntegerSum_add_coreDeficit_le_baseline
      (A := A) (N := N) (m := m)
      hm hA

  omega

/--
The finite target `finiteTargetDeficit (N/m)` subtracts from the complete
5-adic chain, not merely from its first two layers.
-/
theorem finiteTarget_plus_coreIntegerSum_le_baseline
    {A : List Nat}
    {N m : Nat}
    (hm : GoodThirtyCore m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    finiteTargetDeficit (N / m) +
        CoreIntegerSum A N m
      ≤ CoreBaselineSum N m := by

  by_cases hZero :
      finiteTargetDeficit (N / m) = 0

  · have hWhole :=
      coreIntegerSum_add_coreDeficit_le_baseline
        (A := A) (N := N) (m := m)
        hm hA

    rw [hZero, zero_add]

    exact le_trans
      (Nat.le_add_right
        (CoreIntegerSum A N m)
        (CoreDeficitSum A N m))
      hWhole

  · have hPos :
        0 < finiteTargetDeficit (N / m) :=
      Nat.pos_of_ne_zero hZero

    have hSub :
        Finset.range (1 + 1) ⊆
          CoreDepthFinset N m := by
      simpa using
        (finiteTarget_range_subset_coreDepthFinset
          (N := N) (m := m)
          hm hPos)

    have hTarget :
        finiteTargetDeficit (N / m) ≤
          PrefixDeficit
            (FiberSliceDeficit
              (N / m)
              (ActualFiveSlice A N m))
            1 :=
      finiteTargetDeficit_le_actualFiveFiber
        (A := A) (N := N) (m := m)
        hm.1 hA

    exact
      target_plus_coreIntegerSum_le_baseline_of_prefix
        (A := A) (N := N) (m := m)
        (r := 1)
        (target := finiteTargetDeficit (N / m))
        hm hA hSub hTarget

/--
For every high outer scale `N/m ≥ 120`, the canonical high target also
subtracts from the complete finite 5-adic chain. The returned `n` is the
canonical first depth whose normalized scale lies in `24..119`.
-/
theorem exists_canonical_highTarget_plus_coreIntegerSum_le_baseline
    {A : List Nat}
    {N m : Nat}
    (hm : GoodThirtyCore m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (ht : 120 ≤ N / m) :
    ∃ n : Nat,
      1 ≤ n ∧
      24 ≤ FiveScale (N / m) n ∧
      FiveScale (N / m) n ≤ 119 ∧
      highFiberTarget n (FiveScale (N / m) n) +
          CoreIntegerSum A N m
        ≤ CoreBaselineSum N m := by

  rcases
    exists_canonical_five_scale
      (t := N / m) ht
    with
      ⟨n, hn, hLower, hUpper, hHigh⟩

  let r :=
    highSafeDepth n (FiveScale (N / m) n)

  have hFinal :
      1 ≤ FiveScale (N / m) r := by
    dsimp [r]
    exact
      fiveScale_highSafeDepth_pos
        hLower hUpper

  have hSub :
      Finset.range (r + 1) ⊆
        CoreDepthFinset N m :=
    range_subset_coreDepthFinset_of_final_scale_pos
      hm hFinal

  have hTarget :
      highFiberTarget n (FiveScale (N / m) n) ≤
        PrefixDeficit
          (FiberSliceDeficit
            (N / m)
            (ActualFiveSlice A N m))
          r := by
    dsimp [r]
    exact
      highTarget_le_actualFiveFiber_safe
        (A := A) (N := N) (m := m) (n := n)
        hm.1 hA hHigh

  have hWhole :
      highFiberTarget n (FiveScale (N / m) n) +
          CoreIntegerSum A N m
        ≤ CoreBaselineSum N m :=
    target_plus_coreIntegerSum_le_baseline_of_prefix
      (A := A) (N := N) (m := m)
      (r := r)
      (target :=
        highFiberTarget n (FiveScale (N / m) n))
      hm hA hSub hTarget

  exact
    ⟨n, hn, hLower, hUpper, hWhole⟩

end Erdos536813
