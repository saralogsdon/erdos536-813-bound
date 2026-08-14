import Erdos536813.FastTwoLayerCore

namespace Erdos536813

theorem fiberRegion_54_axis_count :
    ((Erdos536.FiberRegionList 1 54).filter
      Erdos536.GridPoint.axisBool).length = 9 := by
  native_decide

theorem fiberRegion_10_axis_count_for_54 :
    ((Erdos536.FiberRegionList 1 10).filter
      Erdos536.GridPoint.axisBool).length = 6 := by
  native_decide

theorem fast_twoLayer_54_deficit_two_bool :
    FastTwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 54)
      (Erdos536.FiberRegionList 1 10)
      9 6 = true := by
  native_decide

theorem selected_twoLayer_54_deficit_two
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
      Lower.Subset (Erdos536.FiberRegionList 1 54))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 10)) :
    Lower.length + Upper.length + 2 ≤ 15 := by
  exact selected_twoLayer_deficit_two_of_fast_certificate
    (by decide : 1 ≤ (9 : Nat))
    (by decide : 1 ≤ (6 : Nat))
    hq hA
    fast_twoLayer_54_deficit_two_bool
    fiberRegion_54_axis_count
    fiberRegion_10_axis_count_for_54
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

end Erdos536813
