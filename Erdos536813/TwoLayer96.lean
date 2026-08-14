import Erdos536813.CardinalityFastTwoLayerCore

namespace Erdos536813

theorem fiberRegion_96_axis_count :
    ((Erdos536.FiberRegionList 1 96).filter
      Erdos536.GridPoint.axisBool).length = 11 := by
  native_decide

theorem fiberRegion_19_axis_count_for_96 :
    ((Erdos536.FiberRegionList 1 19).filter
      Erdos536.GridPoint.axisBool).length = 7 := by
  native_decide

theorem cardinality_fast_twoLayer_96_deficit_two_bool :
    CardinalityFastTwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 96)
      (Erdos536.FiberRegionList 1 19)
      11 7 = true := by
  native_decide

theorem selected_twoLayer_96_deficit_two
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
      Lower.Subset (Erdos536.FiberRegionList 1 96))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 19)) :
    Lower.length + Upper.length + 2 ≤ 18 := by
  exact selected_twoLayer_deficit_two_of_cardinality_fast_certificate
    (by decide : 1 ≤ (11 : Nat))
    (by decide : 1 ≤ (7 : Nat))
    hq hA
    cardinality_fast_twoLayer_96_deficit_two_bool
    fiberRegion_96_axis_count
    fiberRegion_19_axis_count_for_96
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

end Erdos536813
