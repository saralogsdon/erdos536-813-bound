import Erdos536813.TwoLayerCore

namespace Erdos536813

/- Small axis-count certificates used below. -/

theorem fiberRegion_48_axis_count :
    ((Erdos536.FiberRegionList 1 48).filter
      Erdos536.GridPoint.axisBool).length = 9 := by
  native_decide

theorem fiberRegion_54_axis_count :
    ((Erdos536.FiberRegionList 1 54).filter
      Erdos536.GridPoint.axisBool).length = 9 := by
  native_decide

theorem fiberRegion_60_axis_count :
    ((Erdos536.FiberRegionList 1 60).filter
      Erdos536.GridPoint.axisBool).length = 9 := by
  native_decide

theorem fiberRegion_64_axis_count :
    ((Erdos536.FiberRegionList 1 64).filter
      Erdos536.GridPoint.axisBool).length = 10 := by
  native_decide

theorem fiberRegion_9_axis_count :
    ((Erdos536.FiberRegionList 1 9).filter
      Erdos536.GridPoint.axisBool).length = 6 := by
  native_decide

theorem fiberRegion_10_axis_count :
    ((Erdos536.FiberRegionList 1 10).filter
      Erdos536.GridPoint.axisBool).length = 6 := by
  native_decide

theorem fiberRegion_12_axis_count :
    ((Erdos536.FiberRegionList 1 12).filter
      Erdos536.GridPoint.axisBool).length = 6 := by
  native_decide

/- Exact two-layer Boolean certificates. -/

theorem twoLayer_48_deficit_two_bool :
    TwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 48)
      (Erdos536.FiberRegionList 1 9)
      9 6 = true := by
  native_decide

theorem twoLayer_54_deficit_two_bool :
    TwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 54)
      (Erdos536.FiberRegionList 1 10)
      9 6 = true := by
  native_decide

theorem twoLayer_60_deficit_two_bool :
    TwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 60)
      (Erdos536.FiberRegionList 1 12)
      9 6 = true := by
  native_decide

theorem twoLayer_64_deficit_two_bool :
    TwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 64)
      (Erdos536.FiberRegionList 1 12)
      10 6 = true := by
  native_decide

/- Selected-fiber mathematical consequences. -/

theorem selected_twoLayer_48_deficit_two
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
      Lower.Subset (Erdos536.FiberRegionList 1 48))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 9)) :
    Lower.length + Upper.length + 2 ≤ 15 := by
  exact selected_twoLayer_deficit_two_of_certificate
    (by decide : 1 ≤ (9 : Nat))
    (by decide : 1 ≤ (6 : Nat))
    hq hA
    twoLayer_48_deficit_two_bool
    fiberRegion_48_axis_count
    fiberRegion_9_axis_count
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

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
  exact selected_twoLayer_deficit_two_of_certificate
    (by decide : 1 ≤ (9 : Nat))
    (by decide : 1 ≤ (6 : Nat))
    hq hA
    twoLayer_54_deficit_two_bool
    fiberRegion_54_axis_count
    fiberRegion_10_axis_count
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

theorem selected_twoLayer_60_deficit_two
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
      Lower.Subset (Erdos536.FiberRegionList 1 60))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 12)) :
    Lower.length + Upper.length + 2 ≤ 15 := by
  exact selected_twoLayer_deficit_two_of_certificate
    (by decide : 1 ≤ (9 : Nat))
    (by decide : 1 ≤ (6 : Nat))
    hq hA
    twoLayer_60_deficit_two_bool
    fiberRegion_60_axis_count
    fiberRegion_12_axis_count
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

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
  exact selected_twoLayer_deficit_two_of_certificate
    (by decide : 1 ≤ (10 : Nat))
    (by decide : 1 ≤ (6 : Nat))
    hq hA
    twoLayer_64_deficit_two_bool
    fiberRegion_64_axis_count
    fiberRegion_12_axis_count
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

end Erdos536813
