import Erdos536813.AnnulusTheory
import Erdos536813.DeficitChain

namespace Erdos536813

/-!
# Slice deficits and extremality

This file introduces the numerical deficit of one 2,3-smooth slice relative
to the ordinary Gamma-free benchmark `L23 T`.

It also proves the generic extremality bridge needed later:

* if a Gamma-free slice has deficit zero,
* and every Gamma-free subset of the same board has size at most `L23 T`,

then that slice is maximum-cardinality in the board.

The next file will instantiate this bridge for the actual 5-adic inner board
and feed it to `maximum_upper_forces_lower_deficit_two`.
-/

/-- Deficit of a selected slice relative to the one-slice benchmark. -/
def SliceDeficit (T : Nat) (S : List Erdos536.GridPoint) : Nat :=
  L23 T - S.length

/--
When the ordinary one-slice cardinality bound is known, deficit zero is
equivalent to attaining the benchmark exactly.
-/
theorem sliceDeficit_zero_iff_length_eq
    {T : Nat}
    {S : List Erdos536.GridPoint}
    (hBound : S.length ≤ L23 T) :
    SliceDeficit T S = 0 ↔ S.length = L23 T := by
  unfold SliceDeficit
  omega

/-- The deficit is at least `r` exactly when the slice misses at least `r`. -/
theorem le_sliceDeficit_of_length_add_le
    {T r : Nat}
    {S : List Erdos536.GridPoint}
    (h : S.length + r ≤ L23 T) :
    r ≤ SliceDeficit T S := by
  unfold SliceDeficit
  omega

/--
Generic maximum-cardinality constructor: if `S` attains a numerical bound
that is valid for every Gamma-free subset of `D`, then `S` is maximum
Gamma-free in `D`.
-/
theorem maximumGammaFreeIn_of_attains_bound
    {D S : List Erdos536.GridPoint}
    {B : Nat}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset D)
    (hLen : S.length = B)
    (hUniversal :
      ∀ U : List Erdos536.GridPoint,
        Erdos536.GammaFree U →
        U.Subset D →
        U.length ≤ B) :
    MaximumGammaFreeIn D S := by
  refine ⟨hGamma, hSub, ?_⟩
  intro U hUGamma hUSub
  rw [hLen]
  exact hUniversal U hUGamma hUSub

/--
Zero deficit plus a valid `L23 T` upper bound makes a Gamma-free slice
maximum-cardinality in its board.
-/
theorem maximumGammaFreeIn_of_zero_sliceDeficit
    {T : Nat}
    {D S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset D)
    (hUniversal :
      ∀ U : List Erdos536.GridPoint,
        Erdos536.GammaFree U →
        U.Subset D →
        U.length ≤ L23 T)
    (hZero : SliceDeficit T S = 0) :
    MaximumGammaFreeIn D S := by
  have hBound : S.length ≤ L23 T :=
    hUniversal S hGamma hSub
  have hLen : S.length = L23 T :=
    (sliceDeficit_zero_iff_length_eq hBound).1 hZero
  exact maximumGammaFreeIn_of_attains_bound
    hGamma hSub hLen hUniversal

end Erdos536813
