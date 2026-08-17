import Erdos536813.PositiveDepthHighWeight

namespace Erdos536813

/--
The residues in `[0,30)` that are coprime to `30`.
-/
def ThirtyCoprimeResidues : Finset Nat :=
  (Finset.range 30).filter
    (fun r => Nat.gcd r 30 = 1)

/-- Membership in the residue finset has the expected characterization. -/
theorem mem_thirtyCoprimeResidues
    {r : Nat} :
    r ∈ ThirtyCoprimeResidues ↔
      r < 30 ∧ Nat.Coprime r 30 := by

  simp [
    ThirtyCoprimeResidues,
    Nat.Coprime
  ]

/--
There are exactly eight residue classes modulo `30` that are coprime to
`30`.
-/
theorem thirtyCoprimeResidues_card :
    ThirtyCoprimeResidues.card = 8 := by

  native_decide

/-- The resulting natural density is exactly `4/15`. -/
theorem thirtyCoprimeResidues_density :
    (ThirtyCoprimeResidues.card : ℚ) / 30
      =
    (4 / 15 : ℚ) := by

  rw [thirtyCoprimeResidues_card]
  norm_num

end Erdos536813
