import Erdos536813.FastTwoLayerCore

namespace Erdos536813

theorem fiberRegion_81_axis_count :
    ((Erdos536.FiberRegionList 1 81).filter
      Erdos536.GridPoint.axisBool).length = 11 := by
  native_decide

theorem fiberRegion_16_axis_count_for_81 :
    ((Erdos536.FiberRegionList 1 16).filter
      Erdos536.GridPoint.axisBool).length = 7 := by
  native_decide

theorem fast_twoLayer_81_deficit_two_bool :
    FastTwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 81)
      (Erdos536.FiberRegionList 1 16)
      11 7 = true := by
  native_decide

theorem selected_twoLayer_81_deficit_two
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
      Lower.Subset (Erdos536.FiberRegionList 1 81))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 16)) :
    Lower.length + Upper.length + 2 ≤ 18 := by
  exact selected_twoLayer_deficit_two_of_fast_certificate
    (by decide : 1 ≤ (11 : Nat))
    (by decide : 1 ≤ (7 : Nat))
    hq hA
    fast_twoLayer_81_deficit_two_bool
    fiberRegion_81_axis_count
    fiberRegion_16_axis_count_for_81
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

end Erdos536813
