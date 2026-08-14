import Erdos536813.TwoLayerCore

namespace Erdos536813

/-!
### First exact state: `T = 45`

This is the first critical two-layer board.  The lower ordinary bound is
`L23 45 = 9`, and the upper board is `T/5 = 9` with bound `L23 9 = 6`.
-/

theorem fiberRegion_45_gamma_bound_bool :
    GammaFreeSubsetBoundBool
      (Erdos536.FiberRegionList 1 45) 9 = true := by
  native_decide

theorem fiberRegion_9_gamma_bound_bool :
    GammaFreeSubsetBoundBool
      (Erdos536.FiberRegionList 1 9) 6 = true := by
  native_decide

theorem twoLayer_45_deficit_two_bool :
    TwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 45)
      (Erdos536.FiberRegionList 1 9)
      9 6 = true := by
  native_decide

/-- Exact two-layer combinatorial lemma at the critical state `T = 45`. -/
theorem twoLayer_45_deficit_two
    {Lower Upper : List Erdos536.GridPoint}
    (hLowerGamma : Erdos536.GammaFree Lower)
    (hLowerSub :
      Lower.Subset (Erdos536.FiberRegionList 1 45))
    (hUpperGamma : Erdos536.GammaFree Upper)
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 9))
    (hFree : TwoLayerTriangleFree Lower Upper) :
    Lower.length + Upper.length + 2 ≤ 15 := by
  have hLowerBound : Lower.length ≤ 9 :=
    gammaFree_length_le_of_subsetBoundBool
      fiberRegion_45_gamma_bound_bool hLowerGamma hLowerSub
  have hUpperBound : Upper.length ≤ 6 :=
    gammaFree_length_le_of_subsetBoundBool
      fiberRegion_9_gamma_bound_bool hUpperGamma hUpperSub
  exact twoLayer_deficit_two_of_certificate
    (by decide : 1 ≤ (9 : Nat))
    (by decide : 1 ≤ (6 : Nat))
    twoLayer_45_deficit_two_bool
    hLowerGamma hLowerSub hLowerBound
    hUpperGamma hUpperSub hUpperBound
    hFree

/--
Selected-fiber formulation of the `T = 45` exact two-layer lemma.
-/
theorem selected_twoLayer_45_deficit_two
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
      Lower.Subset (Erdos536.FiberRegionList 1 45))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 9)) :
    Lower.length + Upper.length + 2 ≤ 15 := by
  have hLowerGamma : Erdos536.GammaFree Lower :=
    Erdos536.fiberSelected_gammaFree hq hA hLowerSelected
  have h5q : 0 < 5 * q := by
    exact Nat.mul_pos (by decide : 0 < (5 : Nat)) hq
  have hUpperGamma : Erdos536.GammaFree Upper :=
    Erdos536.fiberSelected_gammaFree h5q hA hUpperSelected
  have hFree : TwoLayerTriangleFree Lower Upper :=
    twoLayerTriangleFree_of_selected
      hq hA hLowerSelected hUpperSelected
  exact twoLayer_45_deficit_two
    hLowerGamma hLowerSub hUpperGamma hUpperSub hFree

end Erdos536813
