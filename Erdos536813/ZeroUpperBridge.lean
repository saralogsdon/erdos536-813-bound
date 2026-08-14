import Erdos536813.InnerBoard

namespace Erdos536813

/-!
# Zero upper deficit forces two units of lower deficit

This file connects the abstract slice-deficit language to the already-proved
adjacent-layer theorem.

The only remaining generic input is the ordinary one-slice cardinality bound
for the upper board:

    every Gamma-free subset of `FiveInnerBoardList T`
    has length at most `L23 (T / 5)`.

Once that bound is supplied, zero upper deficit implies that the upper slice
is maximum-cardinality Gamma-free, so the adjacent-layer theorem yields two
units of lower deficit.
-/

/--
If the adjacent upper slice has zero deficit and the usual `L23 (T / 5)`
one-slice upper bound holds on the inner board, then the lower slice has
deficit at least two.
-/
theorem zero_upper_deficit_forces_lower_deficit_two
    {T q N : Nat}
    {A : List Nat}
    {Upper Lower : List Erdos536.GridPoint}
    (hT : 120 ≤ T)
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete Upper A (5 * q))
    (hUpperSub :
      Upper.Subset (FiveInnerBoardList T))
    (hUpperBound :
      ∀ U : List Erdos536.GridPoint,
        Erdos536.GammaFree U →
        U.Subset (FiveInnerBoardList T) →
        U.length ≤ L23 (T / 5))
    (hUpperZero :
      SliceDeficit (T / 5) Upper = 0)
    (hLowerSelected :
      Erdos536.FiberSelectedComplete Lower A q)
    (hLowerBound :
      ∀ p ∈ Lower, Erdos536.fiberValue 1 p ≤ T) :
    2 ≤ SliceDeficit T Lower := by
  have h5q : 0 < 5 * q := by
    exact Nat.mul_pos (by decide : 0 < (5 : Nat)) hq

  have hUpperGamma : Erdos536.GammaFree Upper :=
    Erdos536.fiberSelected_gammaFree h5q hA hUpperSelected

  have hUpperMaximum :
      MaximumGammaFreeIn (FiveInnerBoardList T) Upper := by
    exact
      maximumGammaFreeIn_of_zero_sliceDeficit
        hUpperGamma hUpperSub hUpperBound hUpperZero

  have hLowerMissTwo :
      Lower.length + 2 ≤ L23 T := by
    exact
      maximum_upper_forces_lower_deficit_two
        hT hq hA hUpperSelected hUpperMaximum
        hLowerSelected hLowerBound

  exact le_sliceDeficit_of_length_add_le hLowerMissTwo

end Erdos536813
