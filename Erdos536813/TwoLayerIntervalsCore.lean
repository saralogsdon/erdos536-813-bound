import Erdos536813.AnnulusTheory

namespace Erdos536813

/-!
## Finite two-layer interval interpolation

The exact two-layer configuration at scale `T` depends on the lower board
`D(T)` and the upper board `D(T / 5)`.  In the two finite ranges used by the
global deficit argument,

    45 ≤ T ≤ 71     or     80 ≤ T ≤ 119,

these two boards change only at the ten critical representatives

    45, 48, 54, 60, 64, 80, 81, 90, 96, 108.

This file contains no expensive two-layer search.  It only kernel-checks that
every `T` in the finite ranges has exactly the same two boards, and the same
ordinary one-layer benchmark, as its critical representative.
-/

/-- The finite scales at which the adjacent-layer deficit-two lemma is used. -/
def InFiniteTwoLayerRange (T : Nat) : Prop :=
  (45 ≤ T ∧ T ≤ 71) ∨ (80 ≤ T ∧ T ≤ 119)

/-- The critical state representing the two-layer board at scale `T`. -/
def FiniteTwoLayerRepresentative (T : Nat) : Nat :=
  if T < 48 then 45
  else if T < 54 then 48
  else if T < 60 then 54
  else if T < 64 then 60
  else if T < 72 then 64
  else if T < 81 then 80
  else if T < 90 then 81
  else if T < 96 then 90
  else if T < 108 then 96
  else 108

/-- The ordinary sum of the two one-layer Gamma-free benchmarks. -/
def TwoLayerBenchmark (T : Nat) : Nat :=
  L23 T + L23 (T / 5)

/--
Throughout the finite two-layer ranges, the lower `2,3`-smooth board is
identical to the board at the critical representative.
-/
theorem finiteTwoLayer_lower_board_eq_representative
    {T : Nat}
    (hT : InFiniteTwoLayerRange T) :
    Erdos536.FiberRegionList 1 T =
      Erdos536.FiberRegionList 1 (FiniteTwoLayerRepresentative T) := by
  unfold InFiniteTwoLayerRange at hT
  rcases hT with hT | hT
  · rcases hT with ⟨hLo, hHi⟩
    interval_cases T <;> native_decide
  · rcases hT with ⟨hLo, hHi⟩
    interval_cases T <;> native_decide

/--
Throughout the finite two-layer ranges, the adjacent upper board `D(T/5)` is
identical to the upper board at the critical representative.
-/
theorem finiteTwoLayer_upper_board_eq_representative
    {T : Nat}
    (hT : InFiniteTwoLayerRange T) :
    Erdos536.FiberRegionList 1 (T / 5) =
      Erdos536.FiberRegionList 1 (FiniteTwoLayerRepresentative T / 5) := by
  unfold InFiniteTwoLayerRange at hT
  rcases hT with hT | hT
  · rcases hT with ⟨hLo, hHi⟩
    interval_cases T <;> native_decide
  · rcases hT with ⟨hLo, hHi⟩
    interval_cases T <;> native_decide

/--
The ordinary two-layer benchmark is constant on each critical-state interval.
-/
theorem finiteTwoLayer_benchmark_eq_representative
    {T : Nat}
    (hT : InFiniteTwoLayerRange T) :
    TwoLayerBenchmark T =
      TwoLayerBenchmark (FiniteTwoLayerRepresentative T) := by
  unfold InFiniteTwoLayerRange at hT
  rcases hT with hT | hT
  · rcases hT with ⟨hLo, hHi⟩
    interval_cases T <;>
      native_decide
  · rcases hT with ⟨hLo, hHi⟩
    interval_cases T <;>
      native_decide

/--
A lower/upper subset at the actual scale can be transported verbatim to the
critical representative, because both ambient boards are equal.
-/
theorem finiteTwoLayer_subsets_transfer_to_representative
    {T : Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hT : InFiniteTwoLayerRange T)
    (hLower :
      Lower.Subset (Erdos536.FiberRegionList 1 T))
    (hUpper :
      Upper.Subset (Erdos536.FiberRegionList 1 (T / 5))) :
    Lower.Subset
        (Erdos536.FiberRegionList 1
          (FiniteTwoLayerRepresentative T)) ∧
      Upper.Subset
        (Erdos536.FiberRegionList 1
          (FiniteTwoLayerRepresentative T / 5)) := by
  constructor
  · rw [← finiteTwoLayer_lower_board_eq_representative hT]
    exact hLower
  · rw [← finiteTwoLayer_upper_board_eq_representative hT]
    exact hUpper

end Erdos536813
