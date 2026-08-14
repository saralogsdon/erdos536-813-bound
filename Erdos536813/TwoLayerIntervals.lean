import Erdos536813.TwoLayerIntervalsBefore108
import Erdos536813.TwoLayer108

namespace Erdos536813

/-!
## Full finite adjacent-layer deficit theorem

The ten critical two-layer states are now certified.  The interpolation core
shows that every scale in

    45 ≤ T ≤ 71    or    80 ≤ T ≤ 119

has the same pair of boards and the same one-layer benchmark as one of those
critical representatives.  The theorem below packages the finite part into a
single uniform statement.
-/

/-- The benchmark at the final representative is exactly 18. -/
theorem twoLayerBenchmark_108 :
    TwoLayerBenchmark 108 = 18 := by
  native_decide

/--
Uniform adjacent-layer deficit-two theorem on the complete finite range used
by the global bookkeeping argument.
-/
theorem selected_twoLayer_finite_range_deficit_two
    {T q N : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hT : InFiniteTwoLayerRange T)
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

  by_cases h107 : T ≤ 107

  · have hBefore : InFiniteTwoLayerRangeBefore108 T := by
      rcases hT with hFirst | hSecond
      · exact Or.inl hFirst
      · exact Or.inr ⟨hSecond.1, h107⟩
    exact
      selected_twoLayer_finite_range_before108_deficit_two
        hBefore hq hA
        hLowerSelected hUpperSelected
        hLowerSub hUpperSub

  · have h108 : 108 ≤ T := by
      omega

    have h48 : ¬ T < 48 := by omega
    have h54 : ¬ T < 54 := by omega
    have h60 : ¬ T < 60 := by omega
    have h64 : ¬ T < 64 := by omega
    have h72 : ¬ T < 72 := by omega
    have h81 : ¬ T < 81 := by omega
    have h90 : ¬ T < 90 := by omega
    have h96 : ¬ T < 96 := by omega
    have h108not : ¬ T < 108 := by omega

    have hRep : FiniteTwoLayerRepresentative T = 108 := by
      simp [FiniteTwoLayerRepresentative,
        h48, h54, h60, h64, h72, h81, h90, h96, h108not]

    rcases
        finiteTwoLayer_subsets_transfer_to_representative
          hT hLowerSub hUpperSub with
      ⟨hLowerRep, hUpperRep⟩

    rw [hRep] at hLowerRep hUpperRep

    have hUpper108 :
        Upper.Subset (Erdos536.FiberRegionList 1 21) := by
      simpa using hUpperRep

    have hAt108 :
        Lower.length + Upper.length + 2 ≤ 18 :=
      selected_twoLayer_108_deficit_two
        hq hA hLowerSelected hUpperSelected
        hLowerRep hUpper108

    have hBenchmarkRep :
        TwoLayerBenchmark T =
          TwoLayerBenchmark (FiniteTwoLayerRepresentative T) :=
      finiteTwoLayer_benchmark_eq_representative hT

    rw [hRep] at hBenchmarkRep

    have hBenchmarkT : TwoLayerBenchmark T = 18 :=
      hBenchmarkRep.trans twoLayerBenchmark_108

    calc
      Lower.length + Upper.length + 2 ≤ 18 := hAt108
      _ = TwoLayerBenchmark T := hBenchmarkT.symm

end Erdos536813
