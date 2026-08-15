import Erdos536813.FiberDeficitChain
import Erdos536813.TwoLayerIntervals

namespace Erdos536813

/-!
# Terminal deficit boosts

The high-scale chain gives one unit of cumulative deficit per high-scale
5-adic transition.  To obtain the sharper global constant we need one
additional unit in certain terminal configurations.

There are two mechanisms.

1. If the terminal scale lies in

       45 ≤ T ≤ 71   or   80 ≤ T ≤ 119,

   the already-certified finite two-layer theorem gives

       d_k + d_{k+1} ≥ 2.

   Combined with the high-scale forcing rule, this raises the cumulative
   lower bound from `n` to `n+1`.

2. If the terminal scale `u` lies in `75..79`, then the next scale is exactly

       floor(u / 5) = 15.

   At scale 15 a weaker one-unit adjacent-layer saving is enough.  This
   saving occurs on the next pair `(d_{n+1}, d_{n+2})`, disjoint from the
   high-scale prefix through `d_n`, and hence again raises the cumulative
   lower bound from `n` to `n+1`.

This is the source of the final high-scale extra range

    [45,71] ∪ [75,119].
-/

/-! ## Converting the certified finite two-layer theorem to slice deficits -/

/--
On the certified finite two-layer range, the two adjacent slice deficits
sum to at least two.
-/
theorem finiteTwoLayer_sliceDeficit_two
    {T q N : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hT : InFiniteTwoLayerRange T)
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hLowerSelected :
      Erdos536.FiberSelectedComplete Lower A q)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete Upper A (5 * q))
    (hLowerSub :
      Lower.Subset (Erdos536.FiberRegionList 1 T))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 (T / 5))) :
    2 ≤ SliceDeficit T Lower + SliceDeficit (T / 5) Upper := by
  have hPair :
      Lower.length + Upper.length + 2 ≤ TwoLayerBenchmark T :=
    selected_twoLayer_finite_range_deficit_two
      hT hq hA hLowerSelected hUpperSelected hLowerSub hUpperSub

  have hLowerGamma : Erdos536.GammaFree Lower :=
    Erdos536.fiberSelected_gammaFree hq hA hLowerSelected

  have h5q : 0 < 5 * q :=
    Nat.mul_pos (by decide : 0 < (5 : Nat)) hq

  have hUpperGamma : Erdos536.GammaFree Upper :=
    Erdos536.fiberSelected_gammaFree h5q hA hUpperSelected

  have hLowerCap : Lower.length ≤ L23 T :=
    gammaFree_fiberRegion_card_le_L23 hLowerGamma hLowerSub

  have hUpperCap : Upper.length ≤ L23 (T / 5) :=
    gammaFree_fiberRegion_card_le_L23 hUpperGamma hUpperSub

  unfold SliceDeficit TwoLayerBenchmark at *
  omega

/-! ## The weak terminal saving at scale 15 -/

/-- Exact finite certificate: a Gamma-free subset of the factor-5 annulus at
scale 15 has at most four points. -/
theorem fiveAnnulus_15_subset_bound_bool :
    GammaFreeSubsetBoundBool (FiveAnnulusList 15) 4 = true := by
  native_decide

theorem gammaFree_fiveAnnulus_15_length_le_four
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList 15)) :
    S.length ≤ 4 := by
  exact
    gammaFree_length_le_of_subsetBoundBool
      fiveAnnulus_15_subset_bound_bool hGamma hSub

/--
At lower scale 15, every adjacent selected pair has total slice deficit
at least one.
-/
theorem selected_twoLayer_15_sliceDeficit_one
    {q N : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hLowerSelected :
      Erdos536.FiberSelectedComplete Lower A q)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete Upper A (5 * q))
    (hLowerSub :
      Lower.Subset (Erdos536.FiberRegionList 1 15))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 3)) :
    1 ≤ SliceDeficit 15 Lower + SliceDeficit 3 Upper := by
  have hLowerGamma : Erdos536.GammaFree Lower :=
    Erdos536.fiberSelected_gammaFree hq hA hLowerSelected

  have h5q : 0 < 5 * q :=
    Nat.mul_pos (by decide : 0 < (5 : Nat)) hq

  have hUpperGamma : Erdos536.GammaFree Upper :=
    Erdos536.fiberSelected_gammaFree h5q hA hUpperSelected

  have hLowerCap : Lower.length ≤ L23 15 :=
    gammaFree_fiberRegion_card_le_L23 hLowerGamma hLowerSub

  have hUpperCap : Upper.length ≤ L23 3 :=
    gammaFree_fiberRegion_card_le_L23 hUpperGamma hUpperSub

  by_cases hUpperZero : SliceDeficit 3 Upper = 0
  · have hUpperInnerSub :
        Upper.Subset (FiveInnerBoardList 15) := by
      apply subset_fiveInnerBoardList_of_subset_div_five
      simpa using hUpperSub

    have hUpperMaximum :
        MaximumGammaFreeIn (FiveInnerBoardList 15) Upper := by
      exact
        maximumGammaFreeIn_of_zero_sliceDeficit
          hUpperGamma hUpperInnerSub
          (fun U hGamma hSub =>
            gammaFree_fiveInnerBoard_card_le_L23 hGamma hSub)
          (by simpa using hUpperZero)

    have hOriginInner : gridOrigin ∈ FiveInnerBoardList 15 := by
      apply gridOrigin_mem_fiveInnerBoardList
      norm_num

    have hEraseGamma :
        Erdos536.GammaFree (Lower.erase gridOrigin) :=
      gammaFree_erase hLowerGamma gridOrigin

    have hEraseAnnulus :
        ∀ p ∈ Lower.erase gridOrigin, InFiveAnnulus 15 p := by
      intro p hpErase
      have hpEraseInfo :
          p ≠ gridOrigin ∧ p ∈ Lower :=
        (hLowerGamma.1.mem_erase_iff).1 hpErase
      have hpNeOrigin := hpEraseInfo.1
      have hpLower := hpEraseInfo.2

      have hpSelected : Erdos536.fiberValue q p ∈ A :=
        (hLowerSelected.2 p).1 hpLower

      have hpNontrivial : Erdos536.fiberValue 1 p ≠ 1 := by
        intro hpOne
        apply hpNeOrigin
        exact (fiberValue_one_eq_one_iff p).1 hpOne

      have hpUpperBound : Erdos536.fiberValue 1 p ≤ 15 :=
        (Erdos536.fiberRegionList_complete
          (m := 1) (N := 15)
          (by decide : 0 < (1 : Nat)) p).1
          (hLowerSub hpLower)

      have hpWindow : 15 < 5 * Erdos536.fiberValue 1 p := by
        by_contra hNotWindow
        have hpInnerIneq :
            5 * Erdos536.fiberValue 1 p ≤ 15 :=
          Nat.le_of_not_gt hNotWindow
        have hpInner : p ∈ FiveInnerBoardList 15 :=
          (mem_fiveInnerBoardList).2 hpInnerIneq
        have hpForbidden : Erdos536.fiberValue q p ∉ A :=
          maximumGammaFree_blocks_every_nontrivial_lower_point
            hq hA hUpperSelected hOriginInner hUpperMaximum
            hpInner hpNontrivial
        exact hpForbidden hpSelected

      exact ⟨hpUpperBound, hpWindow⟩

    have hEraseSub :
        (Lower.erase gridOrigin).Subset (FiveAnnulusList 15) := by
      intro p hp
      exact (mem_fiveAnnulusList).2 (hEraseAnnulus p hp)

    have hEraseLen : (Lower.erase gridOrigin).length ≤ 4 :=
      gammaFree_fiveAnnulus_15_length_le_four
        hEraseGamma hEraseSub

    have hRestore :
        Lower.length ≤ (Lower.erase gridOrigin).length + 1 :=
      length_le_erase_add_one Lower gridOrigin

    have hL15 : L23 15 = 6 := by native_decide
    have hLowerDef : 1 ≤ SliceDeficit 15 Lower := by
      unfold SliceDeficit
      rw [hL15]
      omega

    omega

  · have hUpperDef : 1 ≤ SliceDeficit 3 Upper :=
      Nat.one_le_iff_ne_zero.mpr hUpperZero
    omega

/-! ## Abstract arithmetic for attaching a terminal boost to the high-scale chain -/

/--
A terminal pair deficit of two upgrades the high-scale prefix bound by one.
-/
theorem highScaleChain_with_terminal_pair_two
    (d : Nat → Nat)
    (n : Nat)
    (hforce : ∀ k < n, d (k + 1) = 0 → 2 ≤ d k)
    (hterm : 2 ≤ d n + d (n + 1)) :
    n + 1 ≤ PrefixDeficit d (n + 1) := by
  by_cases hLast : d (n + 1) = 0
  · have hdn : 2 ≤ d n := by
      simpa [hLast] using hterm
    cases n with
    | zero =>
        rw [prefixDeficit_succ d 0, prefixDeficit_zero d]
        omega
    | succ m =>
        have hPrefix : m ≤ PrefixDeficit d m := by
          apply highScaleChain_deficit
          intro k hk hkzero
          apply hforce k
          · omega
          · exact hkzero
        rw [prefixDeficit_succ d (m + 1)]
        rw [prefixDeficit_succ d m]
        simp [hLast]
        omega
  · have hPrefix : n ≤ PrefixDeficit d n :=
      highScaleChain_deficit d n hforce
    have hOne : 1 ≤ d (n + 1) :=
      Nat.one_le_iff_ne_zero.mpr hLast
    rw [prefixDeficit_succ d n]
    omega

/--
A one-unit saving on the *next* pair `(d_{n+1},d_{n+2})` is disjoint from
the high-scale prefix through `d_n`, so it also upgrades the total by one.
-/
theorem highScaleChain_with_next_pair_one
    (d : Nat → Nat)
    (n : Nat)
    (hforce : ∀ k < n, d (k + 1) = 0 → 2 ≤ d k)
    (hterm : 1 ≤ d (n + 1) + d (n + 2)) :
    n + 1 ≤ PrefixDeficit d (n + 2) := by
  have hPrefix : n ≤ PrefixDeficit d n :=
    highScaleChain_deficit d n hforce
  rw [prefixDeficit_succ d (n + 1)]
  rw [prefixDeficit_succ d n]
  omega

/-! ## Actual 5-adic terminal boosts -/

/--
If the terminal scale lies in the strong finite two-layer range, the actual
5-adic fiber has cumulative deficit at least `n+1`.
-/
theorem fiveAdic_terminal_strong_boost
    {t m N n : Nat}
    {A : List Nat}
    {F : Nat → List Erdos536.GridPoint}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hSelected :
      ∀ r : Nat,
        Erdos536.FiberSelectedComplete
          (F r) A (FiveBase m r))
    (hSub :
      ∀ r : Nat,
        (F r).Subset
          (Erdos536.FiberRegionList 1 (FiveScale t r)))
    (hHigh :
      ∀ k < n, 120 ≤ FiveScale t k)
    (hTerminal :
      InFiniteTwoLayerRange (FiveScale t n)) :
    n + 1 ≤ PrefixDeficit (FiberSliceDeficit t F) (n + 1) := by
  have hforce :
      ∀ k < n,
        FiberSliceDeficit t F (k + 1) = 0 →
          2 ≤ FiberSliceDeficit t F k := by
    intro k hk hzero
    exact
      fiveAdic_zero_upper_forces_lower_deficit_two
        hm hA hSelected hSub (hHigh k hk) hzero

  have hq : 0 < FiveBase m n := by
    unfold FiveBase
    exact
      Nat.mul_pos hm
        (Nat.pow_pos (by decide : 0 < (5 : Nat)))

  have hUpperSelected :
      Erdos536.FiberSelectedComplete
        (F (n + 1)) A (5 * FiveBase m n) := by
    simpa [fiveBase_succ] using hSelected (n + 1)

  have hUpperSub :
      (F (n + 1)).Subset
        (Erdos536.FiberRegionList 1 (FiveScale t n / 5)) := by
    simpa [fiveScale_succ] using hSub (n + 1)

  have hterm :
      2 ≤
        FiberSliceDeficit t F n +
          FiberSliceDeficit t F (n + 1) := by
    have h :=
      finiteTwoLayer_sliceDeficit_two
        hTerminal hq hA
        (hSelected n) hUpperSelected
        (hSub n) hUpperSub
    simpa [FiberSliceDeficit, fiveScale_succ] using h

  exact
    highScaleChain_with_terminal_pair_two
      (FiberSliceDeficit t F) n hforce hterm

/--
If the terminal scale lies in `75..79`, then the following scale is exactly
15, where the weak one-unit pair saving supplies the extra deficit.
-/
theorem fiveAdic_terminal_75_79_boost
    {t m N n : Nat}
    {A : List Nat}
    {F : Nat → List Erdos536.GridPoint}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hSelected :
      ∀ r : Nat,
        Erdos536.FiberSelectedComplete
          (F r) A (FiveBase m r))
    (hSub :
      ∀ r : Nat,
        (F r).Subset
          (Erdos536.FiberRegionList 1 (FiveScale t r)))
    (hHigh :
      ∀ k < n, 120 ≤ FiveScale t k)
    (hTerminal :
      75 ≤ FiveScale t n ∧ FiveScale t n ≤ 79) :
    n + 1 ≤ PrefixDeficit (FiberSliceDeficit t F) (n + 2) := by
  have hforce :
      ∀ k < n,
        FiberSliceDeficit t F (k + 1) = 0 →
          2 ≤ FiberSliceDeficit t F k := by
    intro k hk hzero
    exact
      fiveAdic_zero_upper_forces_lower_deficit_two
        hm hA hSelected hSub (hHigh k hk) hzero

  have hScaleNext : FiveScale t (n + 1) = 15 := by
    rw [fiveScale_succ]
    omega

  have hScaleNextNext : FiveScale t (n + 2) = 3 := by
    rw [fiveScale_succ]
    rw [hScaleNext]
    norm_num

  have hq : 0 < FiveBase m (n + 1) := by
    unfold FiveBase
    exact
      Nat.mul_pos hm
        (Nat.pow_pos (by decide : 0 < (5 : Nat)))

  have hUpperSelected :
      Erdos536.FiberSelectedComplete
        (F (n + 2)) A (5 * FiveBase m (n + 1)) := by
    simpa [fiveBase_succ] using hSelected (n + 2)

  have hLowerSub15 :
      (F (n + 1)).Subset
        (Erdos536.FiberRegionList 1 15) := by
    simpa [hScaleNext] using hSub (n + 1)

  have hUpperSub3 :
      (F (n + 2)).Subset
        (Erdos536.FiberRegionList 1 3) := by
    simpa [hScaleNextNext] using hSub (n + 2)

  have hterm :
      1 ≤
        FiberSliceDeficit t F (n + 1) +
          FiberSliceDeficit t F (n + 2) := by
    have h :=
      selected_twoLayer_15_sliceDeficit_one
        hq hA (hSelected (n + 1)) hUpperSelected
        hLowerSub15 hUpperSub3
    simpa [FiberSliceDeficit, hScaleNext, hScaleNextNext] using h

  exact
    highScaleChain_with_next_pair_one
      (FiberSliceDeficit t F) n hforce hterm

end Erdos536813
