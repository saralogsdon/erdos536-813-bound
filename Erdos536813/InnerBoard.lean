import Erdos536813.AdjacentLayer
import Erdos536813.SliceDeficit

namespace Erdos536813

/-!
# The adjacent upper board is the ordinary board at scale `T / 5`

The lower layer is measured at scale `T`. The adjacent upper 5-adic layer
contains exactly those exponent points `p` with

    5 * fiberValue 1 p ≤ T.

For natural numbers this is equivalent to

    fiberValue 1 p ≤ T / 5.

For the later extremality argument we do not need literal equality of the
underlying lists.  What matters is that `FiveInnerBoardList T` is a complete
fiber region at scale `T / 5`, hence downward closed and interchangeable at
the level of membership/subset arguments.
-/

/--
`FiveInnerBoardList T` is a complete ordinary fiber region at scale `T / 5`.
-/
theorem fiveInnerBoardList_complete
    (T : Nat) :
    Erdos536.FiberRegionComplete
      (FiveInnerBoardList T) 1 (T / 5) := by
  intro p
  rw [mem_fiveInnerBoardList]
  change
    5 * Erdos536.fiberValue 1 p ≤ T ↔
      Erdos536.fiberValue 1 p ≤ T / 5
  omega

/-- The adjacent upper board is downward closed. -/
theorem fiveInnerBoardList_downClosed
    (T : Nat) :
    Erdos536.DownClosed (FiveInnerBoardList T) := by
  exact
    Erdos536.fiberRegionComplete_downClosed
      (fiveInnerBoardList_complete T)

/--
Membership in the adjacent upper board is equivalent to membership in
Kenta's ordinary fiber-region list at scale `T / 5`.
-/
theorem mem_fiveInnerBoardList_iff_mem_div_five
    {T : Nat}
    {p : Erdos536.GridPoint} :
    p ∈ FiveInnerBoardList T ↔
      p ∈ Erdos536.FiberRegionList 1 (T / 5) := by
  rw [fiveInnerBoardList_complete T]
  rw [
    Erdos536.fiberRegionList_complete
      (m := 1) (N := T / 5)
      (by decide : 0 < (1 : Nat)) p
  ]

/-- Transfer an ordinary `T / 5` board-subset hypothesis to the inner board. -/
theorem subset_fiveInnerBoardList_of_subset_div_five
    {T : Nat}
    {S : List Erdos536.GridPoint}
    (hS :
      S.Subset (Erdos536.FiberRegionList 1 (T / 5))) :
    S.Subset (FiveInnerBoardList T) := by
  intro p hp
  exact (mem_fiveInnerBoardList_iff_mem_div_five).2 (hS hp)

/-- Transfer an inner-board subset hypothesis to the ordinary `T / 5` board. -/
theorem subset_div_five_of_subset_fiveInnerBoardList
    {T : Nat}
    {S : List Erdos536.GridPoint}
    (hS : S.Subset (FiveInnerBoardList T)) :
    S.Subset (Erdos536.FiberRegionList 1 (T / 5)) := by
  intro p hp
  exact (mem_fiveInnerBoardList_iff_mem_div_five).1 (hS hp)

end Erdos536813
