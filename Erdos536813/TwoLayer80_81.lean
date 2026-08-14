import Erdos536813.FastTwoLayerCore

namespace Erdos536813


/-!
## Fast exact states `T = 80, 81`

The two states share the same upper board `D(16)`.
-/

theorem fiberRegion_80_axis_count :
    ((Erdos536.FiberRegionList 1 80).filter
      Erdos536.GridPoint.axisBool).length = 10 := by
  native_decide

theorem fiberRegion_81_axis_count :
    ((Erdos536.FiberRegionList 1 81).filter
      Erdos536.GridPoint.axisBool).length = 11 := by
  native_decide

theorem fiberRegion_16_axis_count :
    ((Erdos536.FiberRegionList 1 16).filter
      Erdos536.GridPoint.axisBool).length = 7 := by
  native_decide

/--
The ambient boards for `T = 80` contain exactly 82 ordered cross-layer
witnesses.  This is a small sanity check on the optimized witness table.
-/
theorem twoLayer_80_crossWitness_count :
    (CrossWitnesses
      (Erdos536.FiberRegionList 1 80)
      (Erdos536.FiberRegionList 1 16)).length = 82 := by
  native_decide

theorem twoLayer_81_crossWitness_count :
    (CrossWitnesses
      (Erdos536.FiberRegionList 1 81)
      (Erdos536.FiberRegionList 1 16)).length = 82 := by
  native_decide

theorem fast_twoLayer_80_deficit_two_bool :
    FastTwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 80)
      (Erdos536.FiberRegionList 1 16)
      10 7 = true := by
  native_decide

theorem fast_twoLayer_81_deficit_two_bool :
    FastTwoLayerDeficitTwoCertificate
      (Erdos536.FiberRegionList 1 81)
      (Erdos536.FiberRegionList 1 16)
      11 7 = true := by
  native_decide

theorem selected_twoLayer_80_deficit_two
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
      Lower.Subset
        (Erdos536.FiberRegionList 1 80))
    (hUpperSub :
      Upper.Subset
        (Erdos536.FiberRegionList 1 16)) :
    Lower.length + Upper.length + 2 ≤ 17 := by
  exact selected_twoLayer_deficit_two_of_fast_certificate
    (by decide : 1 ≤ (10 : Nat))
    (by decide : 1 ≤ (7 : Nat))
    hq hA
    fast_twoLayer_80_deficit_two_bool
    fiberRegion_80_axis_count
    fiberRegion_16_axis_count
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

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
      Lower.Subset
        (Erdos536.FiberRegionList 1 81))
    (hUpperSub :
      Upper.Subset
        (Erdos536.FiberRegionList 1 16)) :
    Lower.length + Upper.length + 2 ≤ 18 := by
  exact selected_twoLayer_deficit_two_of_fast_certificate
    (by decide : 1 ≤ (11 : Nat))
    (by decide : 1 ≤ (7 : Nat))
    hq hA
    fast_twoLayer_81_deficit_two_bool
    fiberRegion_81_axis_count
    fiberRegion_16_axis_count
    hLowerSelected hUpperSelected
    hLowerSub hUpperSub

end Erdos536813
