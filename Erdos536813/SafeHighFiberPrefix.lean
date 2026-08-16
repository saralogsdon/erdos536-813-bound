import Erdos536813.ActiveBaseFiveGrouping

namespace Erdos536813

/-!
# Safe high-scale prefixes

The earlier high-scale target theorem always extended the deficit prefix to
`n + 2`.  That was convenient locally, but at the smallest canonical
terminal value `FiveScale t n = 24`, the `(n+2)`nd scale can already be
zero.  Since `L23 0 = 1` by convention, we do not want a global argument to
count that artificial zero-scale layer.

This file sharpens the prefix length:

* no terminal bonus: stop at `n`;
* strong terminal bonus: stop at `n+1`;
* special `75..79` terminal bonus: stop at `n+2`.

The resulting endpoint is always a genuine positive scale in the canonical
window `24..119`.
-/

/-- The shortest prefix depth needed to realize the high-scale target. -/
def highSafeDepth (n u : Nat) : Nat :=
  if 75 ≤ u ∧ u ≤ 79 then
    n + 2
  else if InHighExtraRange u then
    n + 1
  else
    n

/--
The high-scale target is already realized by the safe prefix, without
extending unnecessarily to `n+2`.
-/
theorem highFiberTarget_le_safePrefix
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
      PrefixDeficit
        (FiberSliceDeficit t F)
        (highSafeDepth n (FiveScale t n)) := by

  let d := FiberSliceDeficit t F
  change
    highFiberTarget n (FiveScale t n) ≤
      PrefixDeficit d (highSafeDepth n (FiveScale t n))

  by_cases hSpecial :
      75 ≤ FiveScale t n ∧ FiveScale t n ≤ 79

  · have hExtra :
        InHighExtraRange (FiveScale t n) := by
      exact Or.inr ⟨hSpecial.1, by omega⟩

    rw [highFiberTarget, if_pos hExtra]

    have hBoost :
        n + 1 ≤ PrefixDeficit d (n + 2) := by
      simpa [d] using
        (fiveAdic_terminal_75_79_boost
          (t := t) (m := m) (N := N) (n := n)
          (A := A) (F := F)
          hm hA hSelected hSub hHigh hSpecial)

    simpa [highSafeDepth, hSpecial, hExtra] using hBoost

  · by_cases hExtra :
        InHighExtraRange (FiveScale t n)

    · rw [highFiberTarget, if_pos hExtra]

      have hStrong :
          InFiniteTwoLayerRange (FiveScale t n) := by
        rcases hExtra with h45_71 | h75_119
        · exact Or.inl h45_71
        · have h80 : 80 ≤ FiveScale t n := by
            by_contra hNot
            have h79 : FiveScale t n ≤ 79 := by
              omega
            exact hSpecial ⟨h75_119.1, h79⟩
          exact Or.inr ⟨h80, h75_119.2⟩

      have hBoost :
          n + 1 ≤ PrefixDeficit d (n + 1) := by
        simpa [d] using
          (fiveAdic_terminal_strong_boost
            (t := t) (m := m) (N := N) (n := n)
            (A := A) (F := F)
            hm hA hSelected hSub hHigh hStrong)

      simpa [highSafeDepth, hSpecial, hExtra] using hBoost

    · rw [highFiberTarget, if_neg hExtra]
      simp only [Nat.add_zero]

      have hBase :
          n ≤ PrefixDeficit d n := by
        simpa [d] using
          (fiveAdic_highScale_prefix_deficit
            (t := t) (m := m) (N := N) (n := n)
            (A := A) (F := F)
            hm hA hSelected hSub hHigh)

      simpa [highSafeDepth, hSpecial, hExtra] using hBase

/--
For a canonical terminal scale in `24..119`, the safe prefix always ends at
a positive scale.  Thus every layer used by the safe prefix corresponds to
an actual base `m * 5^k ≤ N`.
-/
theorem fiveScale_highSafeDepth_pos
    {t n : Nat}
    (hLower : 24 ≤ FiveScale t n)
    (hUpper : FiveScale t n ≤ 119) :
    1 ≤ FiveScale t (highSafeDepth n (FiveScale t n)) := by

  by_cases hSpecial :
      75 ≤ FiveScale t n ∧ FiveScale t n ≤ 79

  · have hStep1 :
        FiveScale t (n + 1) =
          FiveScale t n / 5 := by
      exact fiveScale_succ t n

    have hStep2 :
        FiveScale t (n + 2) =
          FiveScale t (n + 1) / 5 := by
      simpa [Nat.add_assoc] using
        (fiveScale_succ t (n + 1))

    rw [highSafeDepth, if_pos hSpecial, hStep2, hStep1]
    omega

  · by_cases hExtra :
        InHighExtraRange (FiveScale t n)

    · have hStep :
          FiveScale t (n + 1) =
            FiveScale t n / 5 := by
        exact fiveScale_succ t n

      rw [highSafeDepth, if_neg hSpecial, if_pos hExtra, hStep]

      rcases hExtra with h45_71 | h75_119
      · omega
      · omega

    · rw [highSafeDepth, if_neg hSpecial, if_neg hExtra]
      omega

/--
The safe-prefix target theorem instantiated with the actual selected
5-adic slices.
-/
theorem highTarget_le_actualFiveFiber_safe
    {A : List Nat}
    {N m n : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hHigh :
      ∀ k < n, 120 ≤ FiveScale (N / m) k) :
    highFiberTarget n (FiveScale (N / m) n) ≤
      PrefixDeficit
        (FiberSliceDeficit
          (N / m)
          (ActualFiveSlice A N m))
        (highSafeDepth n (FiveScale (N / m) n)) := by

  exact
    highFiberTarget_le_safePrefix
      (t := N / m) (m := m) (N := N) (n := n)
      (A := A) (F := ActualFiveSlice A N m)
      hm hA
      (actualFiveSlice_selected hm hA)
      (actualFiveSlice_subset_normalized hm hA)
      hHigh

/--
Therefore the high target subtracts directly from the upstream integer
fiber count on a prefix containing only the layers actually needed.
-/
theorem highTarget_plus_actualFiveIntegerSafePrefix_le_baseline
    {A : List Nat}
    {N m n : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hHigh :
      ∀ k < n, 120 ≤ FiveScale (N / m) k) :
    highFiberTarget n (FiveScale (N / m) n) +
        ActualFiveIntegerPrefix A N m
          (highSafeDepth n (FiveScale (N / m) n)) ≤
      FiveBaselinePrefix N m
        (highSafeDepth n (FiveScale (N / m) n)) := by

  have hTarget :=
    highTarget_le_actualFiveFiber_safe
      (A := A) (N := N) (m := m) (n := n)
      hm hA hHigh

  have hPrefix :=
    actualFiveIntegerPrefix_add_deficit_le_baseline
      (A := A) (N := N) (m := m)
      (r := highSafeDepth n (FiveScale (N / m) n))
      hm hA

  omega

/--
For every high initial scale `N / m ≥ 120`, choose the canonical terminal
depth.  The target subtraction then holds on a safe prefix whose final
scale is still positive.
-/
theorem exists_canonical_safe_highTarget_bound
    {A : List Nat}
    {N m : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (ht : 120 ≤ N / m) :
    ∃ n : Nat,
      1 ≤ n ∧
      24 ≤ FiveScale (N / m) n ∧
      FiveScale (N / m) n ≤ 119 ∧
      1 ≤
        FiveScale (N / m)
          (highSafeDepth n (FiveScale (N / m) n)) ∧
      highFiberTarget n (FiveScale (N / m) n) +
          ActualFiveIntegerPrefix A N m
            (highSafeDepth n (FiveScale (N / m) n)) ≤
        FiveBaselinePrefix N m
          (highSafeDepth n (FiveScale (N / m) n)) := by

  rcases
    exists_canonical_five_scale
      (t := N / m) ht
    with
      ⟨n, hn, hLower, hUpper, hHigh⟩

  have hPos :
      1 ≤
        FiveScale (N / m)
          (highSafeDepth n (FiveScale (N / m) n)) :=
    fiveScale_highSafeDepth_pos hLower hUpper

  have hBound :=
    highTarget_plus_actualFiveIntegerSafePrefix_le_baseline
      (A := A) (N := N) (m := m) (n := n)
      hm hA hHigh

  exact
    ⟨n, hn, hLower, hUpper, hPos, hBound⟩

end Erdos536813
