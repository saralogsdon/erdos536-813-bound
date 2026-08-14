import Erdos536813.AdjacentLayer
import Erdos536813.SliceDeficit

namespace Erdos536813

/-!
# The adjacent upper board is the ordinary board at scale `T / 5`

The lower layer is measured at scale `T`.  The adjacent upper 5-adic layer
contains exactly those exponent points `p` with

    5 * fiberValue 1 p ≤ T.

For natural numbers this is equivalent to

    fiberValue 1 p ≤ T / 5.

Thus `FiveInnerBoardList T` is exactly Kenta's ordinary fiber-region list at
scale `T / 5`.
-/

/-- The adjacent upper board is exactly the ordinary board at scale `T / 5`. -/
theorem fiveInnerBoardList_eq_fiberRegionList_div_five
    (T : Nat) :
    FiveInnerBoardList T =
      Erdos536.FiberRegionList 1 (T / 5) := by
  apply List.ext
  intro p
  constructor
  · intro hp
    have hpFive :
        5 * Erdos536.fiberValue 1 p ≤ T :=
      (mem_fiveInnerBoardList).1 hp
    apply
      (Erdos536.fiberRegionList_complete
        (m := 1) (N := T / 5)
        (by decide : 0 < (1 : Nat)) p).2
    change Erdos536.fiberValue 1 p ≤ T / 5
    omega
  · intro hp
    have hpDiv :
        Erdos536.fiberValue 1 p ≤ T / 5 := by
      exact
        (Erdos536.fiberRegionList_complete
          (m := 1) (N := T / 5)
          (by decide : 0 < (1 : Nat)) p).1 hp
    apply (mem_fiveInnerBoardList).2
    omega

/-- `FiveInnerBoardList T` is a complete ordinary fiber region at scale `T / 5`. -/
theorem fiveInnerBoardList_complete
    (T : Nat) :
    Erdos536.FiberRegionComplete
      (FiveInnerBoardList T) 1 (T / 5) := by
  rw [fiveInnerBoardList_eq_fiberRegionList_div_five]
  exact
    Erdos536.fiberRegionList_complete
      (m := 1) (N := T / 5)
      (by decide : 0 < (1 : Nat))

/-- The adjacent upper board is downward closed. -/
theorem fiveInnerBoardList_downClosed
    (T : Nat) :
    Erdos536.DownClosed (FiveInnerBoardList T) := by
  exact
    Erdos536.fiberRegionComplete_downClosed
      (fiveInnerBoardList_complete T)

/-- Transfer an ordinary `T / 5` board-subset hypothesis to the inner board. -/
theorem subset_fiveInnerBoardList_of_subset_div_five
    {T : Nat}
    {S : List Erdos536.GridPoint}
    (hS :
      S.Subset (Erdos536.FiberRegionList 1 (T / 5))) :
    S.Subset (FiveInnerBoardList T) := by
  rw [fiveInnerBoardList_eq_fiberRegionList_div_five]
  exact hS

/-- Transfer an inner-board subset hypothesis to the ordinary `T / 5` board. -/
theorem subset_div_five_of_subset_fiveInnerBoardList
    {T : Nat}
    {S : List Erdos536.GridPoint}
    (hS : S.Subset (FiveInnerBoardList T)) :
    S.Subset (Erdos536.FiberRegionList 1 (T / 5)) := by
  rw [← fiveInnerBoardList_eq_fiberRegionList_div_five]
  exact hS

end Erdos536813
