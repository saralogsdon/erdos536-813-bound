import Mathlib

namespace Erdos536813

/-!
# Abstract high-scale deficit-chain bookkeeping

This file isolates the induction used in the global 5-adic argument.

Think of `d k` as the deficit of the `k`th 5-adic slice. At every high
scale, the adjacent-layer theorem gives the implication

    d (k + 1) = 0  ->  2 ≤ d k.

Thus if the upper slice contributes no deficit, the lower slice contributes
at least two. Otherwise the upper slice itself contributes at least one.
The theorem below packages the resulting one-unit-per-high-scale saving.
-/

/-- Total deficit in slices `0, ..., n`. -/
def PrefixDeficit (d : Nat → Nat) (n : Nat) : Nat :=
  Finset.sum (Finset.range (n + 1)) d

/-- Add the final slice to the prefix deficit. -/
theorem prefixDeficit_succ
    (d : Nat → Nat)
    (n : Nat) :
    PrefixDeficit d (n + 1) =
      PrefixDeficit d n + d (n + 1) := by
  simpa [PrefixDeficit, Nat.add_assoc] using
    (Finset.sum_range_succ d (n + 1))

/-- The zero-length prefix is just its single slice `d 0`. -/
theorem prefixDeficit_zero
    (d : Nat → Nat) :
    PrefixDeficit d 0 = d 0 := by
  simp [PrefixDeficit]

/--
If, for every adjacent pair among the first `n` high-scale transitions,
a zero upper deficit forces at least two units of lower deficit, then the
total deficit through slice `n` is at least `n`.
-/
theorem highScaleChain_deficit
    (d : Nat → Nat) :
    ∀ n : Nat,
      (∀ k < n, d (k + 1) = 0 → 2 ≤ d k) →
      n ≤ PrefixDeficit d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hforce
      cases n with
      | zero =>
          simp [PrefixDeficit]
      | succ n =>
          by_cases hlast : d (n + 1) = 0
          · cases n with
            | zero =>
                have htwo : 2 ≤ d 0 := by
                  apply hforce 0
                  · omega
                  · simpa using hlast
                rw [prefixDeficit_succ d 0]
                rw [prefixDeficit_zero d]
                rw [hlast]
                omega
            | succ m =>
                have hprefix : m ≤ PrefixDeficit d m := by
                  apply ih m
                  · omega
                  · intro k hk hkzero
                    apply hforce k
                    · omega
                    · exact hkzero
                have htwo : 2 ≤ d (m + 1) := by
                  apply hforce (m + 1)
                  · omega
                  · simpa using hlast
                rw [prefixDeficit_succ d (m + 1)]
                rw [prefixDeficit_succ d m]
                simp [hlast]
                omega
          · have hprefix : n ≤ PrefixDeficit d n := by
              apply ih n
              · omega
              · intro k hk hkzero
                apply hforce k
                · omega
                · exact hkzero
            have hone : 1 ≤ d (n + 1) :=
              Nat.one_le_iff_ne_zero.mpr hlast
            rw [prefixDeficit_succ d n]
            omega

end Erdos536813
