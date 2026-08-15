import Erdos536813.FiberDeficitChain

namespace Erdos536813

/-!
# Weak finite terminal ranges

The exact weighted deficit table uses a one-unit saving on the four ranges

    [15,17], [20,35], [40,44], [72,79].

The mechanism is the same as the scale-15 argument already used in
`TerminalBoost.lean`:

* if the upper slice has positive deficit, the adjacent pair already saves 1;
* if the upper slice has zero deficit, it is maximum Gamma-free in the
  factor-5 inner board;
* the blocking lemma then pushes every non-origin lower selected point into
  the factor-5 annulus;
* on the weak finite ranges every Gamma-free annulus family misses at least
  two points relative to `L23 T`;
* restoring the possible origin costs one point, leaving a lower-slice
  deficit of at least one.

The finite annulus boards here are tiny (at most ten points), so all 32
scales are checked directly by one kernel-verified `native_decide`.
-/

/-- The 32 scales on which the weak one-unit adjacent-layer saving is used. -/
def WeakFiniteScales : List Nat :=
  [15, 16, 17, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 40, 41, 42, 43, 44, 72, 73, 74, 75, 76, 77, 78, 79]

/-- Membership predicate for the four weak finite ranges. -/
def InWeakFiniteRange (T : Nat) : Prop :=
  T ∈ WeakFiniteScales

/-- Arithmetic description of the weak finite ranges. -/
theorem inWeakFiniteRange_iff
    {T : Nat} :
    InWeakFiniteRange T ↔
      (15 ≤ T ∧ T ≤ 17) ∨
      (20 ≤ T ∧ T ≤ 35) ∨
      (40 ≤ T ∧ T ≤ 44) ∨
      (72 ≤ T ∧ T ≤ 79) := by
  simp [InWeakFiniteRange, WeakFiniteScales]
  omega

/--
One exhaustive Boolean certificate simultaneously checks every weak finite
scale.  At each listed `T`, every Gamma-free subset of the factor-5 annulus
has size at most `L23 T - 2`.
-/
theorem weakFiniteScales_subset_bound_bool :
    WeakFiniteScales.all
      (fun T =>
        GammaFreeSubsetBoundBool
          (FiveAnnulusList T) (L23 T - 2)) = true := by
  native_decide

/--
Every Gamma-free subset of the factor-5 annulus has deficit at least two
on the weak finite ranges.
-/
theorem gammaFree_fiveAnnulus_weak_deficit_two
    {T : Nat}
    {S : List Erdos536.GridPoint}
    (hT : InWeakFiniteRange T)
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (FiveAnnulusList T)) :
    S.length + 2 ≤ L23 T := by
  have hCert :
      GammaFreeSubsetBoundBool
        (FiveAnnulusList T) (L23 T - 2) = true := by
    exact
      (List.all_eq_true.mp weakFiniteScales_subset_bound_bool)
        T hT

  have hLen : S.length ≤ L23 T - 2 :=
    gammaFree_length_le_of_subsetBoundBool
      hCert hGamma hSub

  have hRange := (inWeakFiniteRange_iff.mp hT)
  have hTwoPow : 2 ^ 1 ≤ T := by
    norm_num
    omega
  have hLog : 1 ≤ Nat.log 2 T :=
    Nat.le_log_of_pow_le
      (by decide : 1 < (2 : Nat)) hTwoPow

  unfold L23 at hLen ⊢
  omega

/--
On every weak finite range, adjacent selected slices have total slice
deficit at least one.
-/
theorem selected_twoLayer_weak_sliceDeficit_one
    {T q N : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hT : InWeakFiniteRange T)
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
    1 ≤ SliceDeficit T Lower + SliceDeficit (T / 5) Upper := by

  have h5q : 0 < 5 * q :=
    Nat.mul_pos (by decide : 0 < (5 : Nat)) hq

  have hUpperGamma : Erdos536.GammaFree Upper :=
    Erdos536.fiberSelected_gammaFree h5q hA hUpperSelected

  by_cases hUpperZero : SliceDeficit (T / 5) Upper = 0
  · have hUpperInnerSub :
        Upper.Subset (FiveInnerBoardList T) := by
      exact subset_fiveInnerBoardList_of_subset_div_five hUpperSub

    have hUpperMaximum :
        MaximumGammaFreeIn (FiveInnerBoardList T) Upper := by
      exact
        maximumGammaFreeIn_of_zero_sliceDeficit
          hUpperGamma hUpperInnerSub
          (fun U hGamma hSub =>
            gammaFree_fiveInnerBoard_card_le_L23 hGamma hSub)
          hUpperZero

    have hRange := (inWeakFiniteRange_iff.mp hT)
    have hFive : 5 ≤ T := by
      omega

    have hOriginInner : gridOrigin ∈ FiveInnerBoardList T :=
      gridOrigin_mem_fiveInnerBoardList hFive

    have hLowerGamma : Erdos536.GammaFree Lower :=
      Erdos536.fiberSelected_gammaFree hq hA hLowerSelected

    have hEraseGamma :
        Erdos536.GammaFree (Lower.erase gridOrigin) :=
      gammaFree_erase hLowerGamma gridOrigin

    have hEraseAnnulus :
        ∀ p ∈ Lower.erase gridOrigin, InFiveAnnulus T p := by
      intro p hpErase

      have hpEraseInfo :
          p ≠ gridOrigin ∧ p ∈ Lower :=
        (hLowerGamma.1.mem_erase_iff).1 hpErase

      have hpNeOrigin : p ≠ gridOrigin :=
        hpEraseInfo.1

      have hpLower : p ∈ Lower :=
        hpEraseInfo.2

      have hpSelected : Erdos536.fiberValue q p ∈ A :=
        (hLowerSelected.2 p).1 hpLower

      have hpNontrivial :
          Erdos536.fiberValue 1 p ≠ 1 := by
        intro hpOne
        apply hpNeOrigin
        exact (fiberValue_one_eq_one_iff p).1 hpOne

      have hpUpperBound :
          Erdos536.fiberValue 1 p ≤ T := by
        exact
          (Erdos536.fiberRegionList_complete
            (m := 1) (N := T)
            (by decide : 0 < (1 : Nat)) p).1
            (hLowerSub hpLower)

      have hpWindow :
          T < 5 * Erdos536.fiberValue 1 p := by
        by_contra hNotWindow

        have hpInnerIneq :
            5 * Erdos536.fiberValue 1 p ≤ T :=
          Nat.le_of_not_gt hNotWindow

        have hpInner :
            p ∈ FiveInnerBoardList T :=
          (mem_fiveInnerBoardList).2 hpInnerIneq

        have hpForbidden :
            Erdos536.fiberValue q p ∉ A :=
          maximumGammaFree_blocks_every_nontrivial_lower_point
            hq hA hUpperSelected hOriginInner hUpperMaximum
            hpInner hpNontrivial

        exact hpForbidden hpSelected

      exact ⟨hpUpperBound, hpWindow⟩

    have hEraseSub :
        (Lower.erase gridOrigin).Subset (FiveAnnulusList T) := by
      intro p hp
      exact (mem_fiveAnnulusList).2 (hEraseAnnulus p hp)

    have hEraseDeficit :
        (Lower.erase gridOrigin).length + 2 ≤ L23 T :=
      gammaFree_fiveAnnulus_weak_deficit_two
        hT hEraseGamma hEraseSub

    have hRestore :
        Lower.length ≤ (Lower.erase gridOrigin).length + 1 :=
      length_le_erase_add_one Lower gridOrigin

    have hLowerMissOne :
        Lower.length + 1 ≤ L23 T := by
      omega

    have hLowerDef :
        1 ≤ SliceDeficit T Lower :=
      le_sliceDeficit_of_length_add_le hLowerMissOne

    omega

  · have hUpperDef :
        1 ≤ SliceDeficit (T / 5) Upper :=
      Nat.one_le_iff_ne_zero.mpr hUpperZero
    omega

/--
Actual 5-adic version of the weak terminal saving.
-/
theorem fiveAdic_terminal_weak_pair_one
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
    (hTerminal :
      InWeakFiniteRange (FiveScale t n)) :
    1 ≤
      FiberSliceDeficit t F n +
        FiberSliceDeficit t F (n + 1) := by

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

  have h :=
    selected_twoLayer_weak_sliceDeficit_one
      hTerminal hq hA
      (hSelected n) hUpperSelected
      (hSub n) hUpperSub

  simpa [FiberSliceDeficit, fiveScale_succ] using h

end Erdos536813
