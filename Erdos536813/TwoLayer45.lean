import Erdos536813.FastTwoLayerCore

namespace Erdos536813

theorem fiberRegion_45_axis_count :
    ((Erdos536.FiberRegionList 1 45).filter
      Erdos536.GridPoint.axisBool).length = 9 := by
  native_decide

theorem fiberRegion_9_axis_count_for_45 :
    ((Erdos536.FiberRegionList 1 9).filter
      Erdos536.GridPoint.axisBool).length = 6 := by
  native_decide

theorem fast_twoLayer_45_deficit_two_bool :
    FastTwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 45)
      (Erdos536.FiberRegionList 1 9)
      9 6 = true := by
  native_decide

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
    gammaFree_fiberRegion_length_le_of_axis_count
      fiberRegion_45_axis_count hLowerGamma hLowerSub
  have hUpperBound : Upper.length ≤ 6 :=
    gammaFree_fiberRegion_length_le_of_axis_count
      fiberRegion_9_axis_count_for_45 hUpperGamma hUpperSub
  exact fast_twoLayer_deficit_two_of_certificate
    (by decide : 1 ≤ (9 : Nat))
    (by decide : 1 ≤ (6 : Nat))
    fast_twoLayer_45_deficit_two_bool
    hLowerGamma hLowerSub hLowerBound
    hUpperGamma hUpperSub hUpperBound
    hFree

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
  exact selected_twoLayer_deficit_two_of_fast_certificate
    (by decide : 1 ≤ (9 : Nat))
    (by decide : 1 ≤ (6 : Nat))
    hq hA
    fast_twoLayer_45_deficit_two_bool
    fiberRegion_45_axis_count
    fiberRegion_9_axis_count_for_45
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

end Erdos536813
