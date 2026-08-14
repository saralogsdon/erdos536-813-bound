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

def InFiniteTwoLayerRangeBefore108 (T : Nat) : Prop :=
  (45 ≤ T ∧ T ≤ 71) ∨ (80 ≤ T ∧ T ≤ 107)

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

  by_cases h48 : T < 48
  · have hRep : FiniteTwoLayerRepresentative T = 45 := by
      simp [FiniteTwoLayerRepresentative, h48]
    rw [hRep] at hLowerRep hUpperRep hBenchmark
    have hUpper45 :
        Upper.Subset (Erdos536.FiberRegionList 1 9) := by
      simpa using hUpperRep
    have hState :
        Lower.length + Upper.length + 2 ≤ 15 :=
      selected_twoLayer_45_deficit_two
        hq hA hLowerSelected hUpperSelected hLowerRep hUpper45
    have hB : TwoLayerBenchmark 45 = 15 := by
      native_decide
    calc
      Lower.length + Upper.length + 2 ≤ 15 := hState
      _ = TwoLayerBenchmark 45 := hB.symm
      _ = TwoLayerBenchmark T := hBenchmark.symm

  · by_cases h54 : T < 54
    · have hRep : FiniteTwoLayerRepresentative T = 48 := by
        simp [FiniteTwoLayerRepresentative, h48, h54]
      rw [hRep] at hLowerRep hUpperRep hBenchmark
      have hUpper48 :
          Upper.Subset (Erdos536.FiberRegionList 1 9) := by
        simpa using hUpperRep
      have hState :
          Lower.length + Upper.length + 2 ≤ 15 :=
        selected_twoLayer_48_deficit_two
          hq hA hLowerSelected hUpperSelected hLowerRep hUpper48
      have hB : TwoLayerBenchmark 48 = 15 := by
        native_decide
      calc
        Lower.length + Upper.length + 2 ≤ 15 := hState
        _ = TwoLayerBenchmark 48 := hB.symm
        _ = TwoLayerBenchmark T := hBenchmark.symm

    · by_cases h60 : T < 60
      · have hRep : FiniteTwoLayerRepresentative T = 54 := by
          simp [FiniteTwoLayerRepresentative, h48, h54, h60]
        rw [hRep] at hLowerRep hUpperRep hBenchmark
        have hUpper54 :
            Upper.Subset (Erdos536.FiberRegionList 1 10) := by
          simpa using hUpperRep
        have hState :
            Lower.length + Upper.length + 2 ≤ 15 :=
          selected_twoLayer_54_deficit_two
            hq hA hLowerSelected hUpperSelected hLowerRep hUpper54
        have hB : TwoLayerBenchmark 54 = 15 := by
          native_decide
        calc
          Lower.length + Upper.length + 2 ≤ 15 := hState
          _ = TwoLayerBenchmark 54 := hB.symm
          _ = TwoLayerBenchmark T := hBenchmark.symm

      · by_cases h64 : T < 64
        · have hRep : FiniteTwoLayerRepresentative T = 60 := by
            simp [FiniteTwoLayerRepresentative, h48, h54, h60, h64]
          rw [hRep] at hLowerRep hUpperRep hBenchmark
          have hUpper60 :
              Upper.Subset (Erdos536.FiberRegionList 1 12) := by
            simpa using hUpperRep
          have hState :
              Lower.length + Upper.length + 2 ≤ 15 :=
            selected_twoLayer_60_deficit_two
              hq hA hLowerSelected hUpperSelected hLowerRep hUpper60
          have hB : TwoLayerBenchmark 60 = 15 := by
            native_decide
          calc
            Lower.length + Upper.length + 2 ≤ 15 := hState
            _ = TwoLayerBenchmark 60 := hB.symm
            _ = TwoLayerBenchmark T := hBenchmark.symm

        · by_cases h72 : T < 72
          · have hRep : FiniteTwoLayerRepresentative T = 64 := by
              simp [FiniteTwoLayerRepresentative,
                h48, h54, h60, h64, h72]
            rw [hRep] at hLowerRep hUpperRep hBenchmark
            have hUpper64 :
                Upper.Subset (Erdos536.FiberRegionList 1 12) := by
              simpa using hUpperRep
            have hState :
                Lower.length + Upper.length + 2 ≤ 16 :=
              selected_twoLayer_64_deficit_two
                hq hA hLowerSelected hUpperSelected hLowerRep hUpper64
            have hB : TwoLayerBenchmark 64 = 16 := by
              native_decide
            calc
              Lower.length + Upper.length + 2 ≤ 16 := hState
              _ = TwoLayerBenchmark 64 := hB.symm
              _ = TwoLayerBenchmark T := hBenchmark.symm

          · by_cases h81 : T < 81
            · have hRep : FiniteTwoLayerRepresentative T = 80 := by
                simp [FiniteTwoLayerRepresentative,
                  h48, h54, h60, h64, h72, h81]
              rw [hRep] at hLowerRep hUpperRep hBenchmark
              have hUpper80 :
                  Upper.Subset (Erdos536.FiberRegionList 1 16) := by
                simpa using hUpperRep
              have hState :
                  Lower.length + Upper.length + 2 ≤ 17 :=
                selected_twoLayer_80_deficit_two
                  hq hA hLowerSelected hUpperSelected hLowerRep hUpper80
              have hB : TwoLayerBenchmark 80 = 17 := by
                native_decide
              calc
                Lower.length + Upper.length + 2 ≤ 17 := hState
                _ = TwoLayerBenchmark 80 := hB.symm
                _ = TwoLayerBenchmark T := hBenchmark.symm

            · by_cases h90 : T < 90
              · have hRep : FiniteTwoLayerRepresentative T = 81 := by
                  simp [FiniteTwoLayerRepresentative,
                    h48, h54, h60, h64, h72, h81, h90]
                rw [hRep] at hLowerRep hUpperRep hBenchmark
                have hUpper81 :
                    Upper.Subset (Erdos536.FiberRegionList 1 16) := by
                  simpa using hUpperRep
                have hState :
                    Lower.length + Upper.length + 2 ≤ 18 :=
                  selected_twoLayer_81_deficit_two
                    hq hA hLowerSelected hUpperSelected hLowerRep hUpper81
                have hB : TwoLayerBenchmark 81 = 18 := by
                  native_decide
                calc
                  Lower.length + Upper.length + 2 ≤ 18 := hState
                  _ = TwoLayerBenchmark 81 := hB.symm
                  _ = TwoLayerBenchmark T := hBenchmark.symm

              · by_cases h96 : T < 96
                · have hRep : FiniteTwoLayerRepresentative T = 90 := by
                    simp [FiniteTwoLayerRepresentative,
                      h48, h54, h60, h64, h72, h81, h90, h96]
                  rw [hRep] at hLowerRep hUpperRep hBenchmark
                  have hUpper90 :
                      Upper.Subset (Erdos536.FiberRegionList 1 18) := by
                    simpa using hUpperRep
                  have hState :
                      Lower.length + Upper.length + 2 ≤ 18 :=
                    selected_twoLayer_90_deficit_two
                      hq hA hLowerSelected hUpperSelected hLowerRep hUpper90
                  have hB : TwoLayerBenchmark 90 = 18 := by
                    native_decide
                  calc
                    Lower.length + Upper.length + 2 ≤ 18 := hState
                    _ = TwoLayerBenchmark 90 := hB.symm
                    _ = TwoLayerBenchmark T := hBenchmark.symm

                · have h108 : T < 108 := by
                    rcases hT with hFirst | hSecond <;> omega
                  have hRep : FiniteTwoLayerRepresentative T = 96 := by
                    simp [FiniteTwoLayerRepresentative,
                      h48, h54, h60, h64, h72, h81, h90, h96, h108]
                  rw [hRep] at hLowerRep hUpperRep hBenchmark
                  have hUpper96 :
                      Upper.Subset (Erdos536.FiberRegionList 1 19) := by
                    simpa using hUpperRep
                  have hState :
                      Lower.length + Upper.length + 2 ≤ 18 :=
                    selected_twoLayer_96_deficit_two
                      hq hA hLowerSelected hUpperSelected hLowerRep hUpper96
                  have hB : TwoLayerBenchmark 96 = 18 := by
                    native_decide
                  calc
                    Lower.length + Upper.length + 2 ≤ 18 := hState
                    _ = TwoLayerBenchmark 96 := hB.symm
                    _ = TwoLayerBenchmark T := hBenchmark.symm

end Erdos536813
