import Erdos536813.WeakFiniteRanges
import Erdos536813.TerminalBoost
import Erdos536813.DeficitArithmetic

namespace Erdos536813

/-!
# Consolidated per-fiber deficit targets

This file packages all local 5-adic combinatorics into the two target
statements used by the global weighted argument.

For finite scales, `finiteTargetDeficit t` is exactly the table already used
in `DeficitArithmetic.lean`.

For high scales, each high-scale transition contributes one unit of deficit,
and terminal scales in

    [45,71] ∪ [75,119]

contribute one additional unit.
-/

/-- The terminal `u`-range that earns the extra high-scale unit. -/
def InHighExtraRange (u : Nat) : Prop :=
  (45 ≤ u ∧ u ≤ 71) ∨ (75 ≤ u ∧ u ≤ 119)

instance instDecidableInHighExtraRange (u : Nat) :
    Decidable (InHighExtraRange u) := by
  unfold InHighExtraRange
  infer_instance

/-- Numerical high-scale target: one unit per high transition, plus the terminal bonus. -/
def highFiberTarget (n u : Nat) : Nat :=
  n + if InHighExtraRange u then 1 else 0

/--
Actual 5-adic form of the strong finite two-layer pair saving.
-/
theorem fiveAdic_strong_pair_two
    {t m N n : Nat}
    {A : List Nat}
    {F : Nat → List Erdos536.GridPoint}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hSelected :
      ∀ r : Nat,
        Erdos536.FiberSelectedComplete
          (F r) A (FiveBase m r))
    (hSub :
      ∀ r : Nat,
        (F r).Subset
          (Erdos536.FiberRegionList 1 (FiveScale t r)))
    (hTerminal :
      InFiniteTwoLayerRange (FiveScale t n)) :
    2 ≤
      FiberSliceDeficit t F n +
        FiberSliceDeficit t F (n + 1) := by

  have hq : 0 < FiveBase m n := by
    unfold FiveBase
    exact
      Nat.mul_pos hm
        (Nat.pow_pos (by decide : 0 < (5 : Nat)))

  have hUpperSelected :
      Erdos536.FiberSelectedComplete
        (F (n + 1)) A (5 * FiveBase m n) := by
    simpa [fiveBase_succ] using hSelected (n + 1)

  have hUpperSub :
      (F (n + 1)).Subset
        (Erdos536.FiberRegionList 1 (FiveScale t n / 5)) := by
    simpa [fiveScale_succ] using hSub (n + 1)

  have h :=
    finiteTwoLayer_sliceDeficit_two
      hTerminal hq hA
      (hSelected n) hUpperSelected
      (hSub n) hUpperSub

  simpa [FiberSliceDeficit, fiveScale_succ] using h

/--
The exact finite target table is realized by the first two actual 5-adic
slices of every fiber.
-/
theorem finiteTargetDeficit_le_fiberPrefix
    {t m N : Nat}
    {A : List Nat}
    {F : Nat → List Erdos536.GridPoint}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hSelected :
      ∀ r : Nat,
        Erdos536.FiberSelectedComplete
          (F r) A (FiveBase m r))
    (hSub :
      ∀ r : Nat,
        (F r).Subset
          (Erdos536.FiberRegionList 1 (FiveScale t r))) :
    finiteTargetDeficit t ≤
      PrefixDeficit (FiberSliceDeficit t F) 1 := by

  let d := FiberSliceDeficit t F

  have hScale0 : FiveScale t 0 = t := by
    simp [FiveScale]

  have hPrefix :
      PrefixDeficit d 1 = d 0 + d 1 := by
    rw [prefixDeficit_succ d 0, prefixDeficit_zero]

  by_cases hStrong :
      (45 ≤ t ∧ t ≤ 71) ∨ (80 ≤ t ∧ t ≤ 119)

  · have hTerminal :
        InFiniteTwoLayerRange (FiveScale t 0) := by
      rw [hScale0]
      exact hStrong

    have hPair :
        2 ≤ d 0 + d 1 := by
      have h :=
        fiveAdic_strong_pair_two
          (t := t) (m := m) (N := N) (n := 0)
          (A := A) (F := F)
          hm hA hSelected hSub hTerminal
      simpa [d] using h

    rw [hPrefix]
    simpa [finiteTargetDeficit, hStrong] using hPair

  · by_cases hWeak :
        (15 ≤ t ∧ t ≤ 17) ∨
        (20 ≤ t ∧ t ≤ 35) ∨
        (40 ≤ t ∧ t ≤ 44) ∨
        (72 ≤ t ∧ t ≤ 79)

    · have hTerminal :
          InWeakFiniteRange (FiveScale t 0) := by
        rw [hScale0]
        exact inWeakFiniteRange_iff.mpr hWeak

      have hPair :
          1 ≤ d 0 + d 1 := by
        have h :=
          fiveAdic_terminal_weak_pair_one
            (t := t) (m := m) (N := N) (n := 0)
            (A := A) (F := F)
            hm hA hSelected hSub hTerminal
        simpa [d] using h

      rw [hPrefix]
      simpa [finiteTargetDeficit, hStrong, hWeak] using hPair

    · simp [finiteTargetDeficit, hStrong, hWeak]

/--
The high-scale target is realized by the actual 5-adic fiber.

The hypotheses `hHigh` say that the first `n` transitions are in the
`T ≥ 120` regime.  The terminal scale itself is allowed to be arbitrary;
the bonus is awarded exactly when it lies in `InHighExtraRange`.
-/
theorem highFiberTarget_le_fiberPrefix
    {t m N n : Nat}
    {A : List Nat}
    {F : Nat → List Erdos536.GridPoint}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hSelected :
      ∀ r : Nat,
        Erdos536.FiberSelectedComplete
          (F r) A (FiveBase m r))
    (hSub :
      ∀ r : Nat,
        (F r).Subset
          (Erdos536.FiberRegionList 1 (FiveScale t r)))
    (hHigh :
      ∀ k < n, 120 ≤ FiveScale t k) :
    highFiberTarget n (FiveScale t n) ≤
      PrefixDeficit (FiberSliceDeficit t F) (n + 2) := by

  let d := FiberSliceDeficit t F

  by_cases hExtra : InHighExtraRange (FiveScale t n)

  · rw [highFiberTarget, if_pos hExtra]

    rcases hExtra with h45_71 | h75_119

    · have hStrong :
          InFiniteTwoLayerRange (FiveScale t n) :=
        Or.inl h45_71

      have hBoost :
          n + 1 ≤ PrefixDeficit d (n + 1) := by
        simpa [d] using
          (fiveAdic_terminal_strong_boost
            (t := t) (m := m) (N := N) (n := n)
            (A := A) (F := F)
            hm hA hSelected hSub hHigh hStrong)

      have hExtend :
          PrefixDeficit d (n + 1) ≤
            PrefixDeficit d (n + 2) := by
        rw [prefixDeficit_succ d (n + 1)]
        omega

      omega

    · by_cases h79 : FiveScale t n ≤ 79

      · have hSpecial :
            75 ≤ FiveScale t n ∧ FiveScale t n ≤ 79 :=
          ⟨h75_119.1, h79⟩

        simpa [d] using
          (fiveAdic_terminal_75_79_boost
            (t := t) (m := m) (N := N) (n := n)
            (A := A) (F := F)
            hm hA hSelected hSub hHigh hSpecial)

      · have h80 : 80 ≤ FiveScale t n := by
          omega

        have hStrong :
            InFiniteTwoLayerRange (FiveScale t n) :=
          Or.inr ⟨h80, h75_119.2⟩

        have hBoost :
            n + 1 ≤ PrefixDeficit d (n + 1) := by
          simpa [d] using
            (fiveAdic_terminal_strong_boost
              (t := t) (m := m) (N := N) (n := n)
              (A := A) (F := F)
              hm hA hSelected hSub hHigh hStrong)

        have hExtend :
            PrefixDeficit d (n + 1) ≤
              PrefixDeficit d (n + 2) := by
          rw [prefixDeficit_succ d (n + 1)]
          omega

        omega

  · rw [highFiberTarget, if_neg hExtra]
    simp only [Nat.add_zero]

    have hBase :
        n ≤ PrefixDeficit d n := by
      simpa [d] using
        (fiveAdic_highScale_prefix_deficit
          (t := t) (m := m) (N := N) (n := n)
          (A := A) (F := F)
          hm hA hSelected hSub hHigh)

    have hExtend1 :
        PrefixDeficit d n ≤ PrefixDeficit d (n + 1) := by
      rw [prefixDeficit_succ d n]
      omega

    have hExtend2 :
        PrefixDeficit d (n + 1) ≤
          PrefixDeficit d (n + 2) := by
      rw [prefixDeficit_succ d (n + 1)]
      omega

    omega

end Erdos536813
