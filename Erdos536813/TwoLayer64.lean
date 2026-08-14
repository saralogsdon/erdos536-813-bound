import Erdos536813.FastTwoLayerCore

namespace Erdos536813

theorem fiberRegion_64_axis_count :
    ((Erdos536.FiberRegionList 1 64).filter
      Erdos536.GridPoint.axisBool).length = 10 := by
  native_decide

theorem fiberRegion_12_axis_count_for_64 :
    ((Erdos536.FiberRegionList 1 12).filter
      Erdos536.GridPoint.axisBool).length = 6 := by
  native_decide

theorem fast_twoLayer_64_deficit_two_bool :
    FastTwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 64)
      (Erdos536.FiberRegionList 1 12)
      10 6 = true := by
  native_decide

theorem selected_twoLayer_64_deficit_two
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
      Lower.Subset (Erdos536.FiberRegionList 1 64))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 12)) :
    Lower.length + Upper.length + 2 ≤ 16 := by
  exact selected_twoLayer_deficit_two_of_fast_certificate
    (by decide : 1 ≤ (10 : Nat))
    (by decide : 1 ≤ (6 : Nat))
    hq hA
    fast_twoLayer_64_deficit_two_bool
    fiberRegion_64_axis_count
    fiberRegion_12_axis_count_for_64
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

end Erdos536813
