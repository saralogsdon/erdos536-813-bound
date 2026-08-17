import Erdos536813.GoodCoreResidues

namespace Erdos536813

/--
A computable list of the residues in `[0,30)` that are coprime to `30`.
-/
def ThirtyCoprimeResidueList : List Nat :=
  (List.range 30).filter
    (fun r => decide (Nat.gcd r 30 = 1))

/-- Membership in the residue list has the expected description. -/
theorem mem_thirtyCoprimeResidueList
    {r : Nat} :
    r ∈ ThirtyCoprimeResidueList ↔
      r < 30 ∧ Nat.Coprime r 30 := by

  simp [
    ThirtyCoprimeResidueList,
    Nat.Coprime
  ]

/-- The residue list has exactly eight entries. -/
theorem thirtyCoprimeResidueList_length :
    ThirtyCoprimeResidueList.length = 8 := by

  native_decide

/-- The residue list has no duplicates. -/
theorem thirtyCoprimeResidueList_nodup :
    ThirtyCoprimeResidueList.Nodup := by

  unfold ThirtyCoprimeResidueList

  exact
    List.nodup_range.filter
      (fun r => decide (Nat.gcd r 30 = 1))

/--
Translate the eight admissible residues into the block beginning at `30*b`.
-/
def GoodCoreResidueBlockList
    (b : Nat) : List Nat :=
  ThirtyCoprimeResidueList.map
    (fun r => 30 * b + r)

/-- Every translated residue block still has exactly eight entries. -/
theorem goodCoreResidueBlockList_length
    (b : Nat) :
    (GoodCoreResidueBlockList b).length = 8 := by

  simp [
    GoodCoreResidueBlockList,
    thirtyCoprimeResidueList_length
  ]

/-- Translation preserves the absence of duplicates. -/
theorem goodCoreResidueBlockList_nodup
    (b : Nat) :
    (GoodCoreResidueBlockList b).Nodup := by

  unfold GoodCoreResidueBlockList

  exact
    thirtyCoprimeResidueList_nodup.map
      (fun r => 30 * b + r)
      (by
        intro r s hrs hEq
        exact hrs (Nat.add_left_cancel hEq))

/-- Membership in a translated residue block has an explicit witness. -/
theorem mem_goodCoreResidueBlockList
    {b m : Nat} :
    m ∈ GoodCoreResidueBlockList b ↔
      ∃ r ∈ ThirtyCoprimeResidueList,
        m = 30 * b + r := by

  simp [GoodCoreResidueBlockList]

end Erdos536813
