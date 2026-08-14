import Erdos536813.TwoLayerIntervalsCore
import Erdos536813.TwoLayer45
import Erdos536813.TwoLayer48
import Erdos536813.TwoLayer54
import Erdos536813.TwoLayer60
import Erdos536813.TwoLayer64
import Erdos536813.TwoLayer80
import Erdos536813.TwoLayer81
import Erdos536813.TwoLayer90
import Erdos536813.TwoLayer96

namespace Erdos536813

/-!
## Uniform finite two-layer deficit before the final `T = 108` block

All critical representatives through `96` are already certified. Combining
those certificates with `TwoLayerIntervalsCore` gives the uniform adjacent-
layer deficit-two theorem on

    45 ≤ T ≤ 71    or    80 ≤ T ≤ 107.

The only omitted finite block is `108 ≤ T ≤ 119`, represented by the final
critical state `T = 108`.
-/

def InFiniteTwoLayerRangeBefore108 (T : Nat) : Prop :=
  (45 ≤ T ∧ T ≤ 71) ∨ (80 ≤ T ∧ T ≤ 107)

/--
Uniform selected-fiber deficit-two theorem on all finite scales whose critical
representative is already kernel-checked (i.e. all finite scales below the
final `T = 108` block).
-/
theorem selected_twoLayer_finite_range_before108_deficit_two
    {T q N : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hT : InFiniteTwoLayerRangeBefore108 T)
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
    Lower.length + Upper.length + 2 ≤ TwoLayerBenchmark T := by

  have hFull : InFiniteTwoLayerRange T := by
    rcases hT with hFirst | hSecond
    · exact Or.inl hFirst
    · exact Or.inr ⟨hSecond.1, Nat.le_trans hSecond.2 (by decide : 107 ≤ 119)⟩

  rcases
      finiteTwoLayer_subsets_transfer_to_representative
        hFull hLowerSub hUpperSub with
    ⟨hLowerRep, hUpperRep⟩

  have hBenchmark :
      TwoLayerBenchmark T =
        TwoLayerBenchmark (FiniteTwoLayerRepresentative T) :=
    finiteTwoLayer_benchmark_eq_representative hFull

  rw [hBenchmark]

  have hLo : 45 ≤ T := by
    rcases hT with hFirst | hSecond <;> omega
  have hHi : T ≤ 107 := by
    rcases hT with hFirst | hSecond <;> omega

  interval_cases T <;>
    try omega <;>
    simp [FiniteTwoLayerRepresentative] at hLowerRep hUpperRep ⊢ <;>
    first
    | simpa [TwoLayerBenchmark, L23, Nat.log] using
        selected_twoLayer_45_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpperRep
    | simpa [TwoLayerBenchmark, L23, Nat.log] using
        selected_twoLayer_48_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpperRep
    | simpa [TwoLayerBenchmark, L23, Nat.log] using
        selected_twoLayer_54_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpperRep
    | simpa [TwoLayerBenchmark, L23, Nat.log] using
        selected_twoLayer_60_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpperRep
    | simpa [TwoLayerBenchmark, L23, Nat.log] using
        selected_twoLayer_64_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpperRep
    | simpa [TwoLayerBenchmark, L23, Nat.log] using
        selected_twoLayer_80_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpperRep
    | simpa [TwoLayerBenchmark, L23, Nat.log] using
        selected_twoLayer_81_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpperRep
    | simpa [TwoLayerBenchmark, L23, Nat.log] using
        selected_twoLayer_90_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpperRep
    | simpa [TwoLayerBenchmark, L23, Nat.log] using
        selected_twoLayer_96_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpperRep

end Erdos536813
