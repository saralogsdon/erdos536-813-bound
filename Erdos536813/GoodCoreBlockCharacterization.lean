import Erdos536813.GoodCoreResidueBlocks

namespace Erdos536813

/--
Adding a multiple of `30` preserves coprimality with `30`.
-/
theorem translated_residue_coprime_thirty
    {b r : Nat}
    (hr : Nat.Coprime r 30) :
    Nat.Coprime (30 * b + r) 30 := by

  exact
    (Nat.coprime_mul_left_add_left r 30 b).mpr
      hr

/--
Every entry in a translated residue block is a good core lying strictly
between the consecutive multiples `30*b` and `30*(b+1)`.
-/
theorem mem_goodCoreResidueBlockList_data
    {b m : Nat}
    (hm : m ∈ GoodCoreResidueBlockList b) :
    30 * b < m ∧
      m < 30 * (b + 1) ∧
      GoodThirtyCore m := by

  rw [mem_goodCoreResidueBlockList] at hm
  rcases hm with ⟨r, hrMem, rfl⟩

  have hrData :=
    mem_thirtyCoprimeResidueList.mp hrMem

  have hrPos :
      0 < r := by
    by_contra hNot
    have hrZero :
        r = 0 :=
      Nat.eq_zero_of_not_pos hNot
    subst r
    simp at hrData

  have hLower :
      30 * b < 30 * b + r := by
    omega

  have hUpper :
      30 * b + r < 30 * (b + 1) := by
    have hrLt :
        r < 30 :=
      hrData.1
    omega

  have hGood :
      GoodThirtyCore (30 * b + r) := by
    constructor
    · omega
    · exact
        translated_residue_coprime_thirty
          hrData.2

  exact ⟨hLower, hUpper, hGood⟩

/--
Conversely, every good core strictly inside the block between `30*b` and
`30*(b+1)` occurs in the translated residue list.
-/
theorem goodCore_mem_residueBlockList
    {b m : Nat}
    (hLower : 30 * b < m)
    (hUpper : m < 30 * (b + 1))
    (hGood : GoodThirtyCore m) :
    m ∈ GoodCoreResidueBlockList b := by

  let r : Nat :=
    m - 30 * b

  have hrPos :
      0 < r := by
    dsimp [r]
    omega

  have hrLt :
      r < 30 := by
    dsimp [r]
    omega

  have hmEq :
      m = 30 * b + r := by
    dsimp [r]
    omega

  have hrCoprime :
      Nat.Coprime r 30 := by
    apply
      (Nat.coprime_mul_left_add_left r 30 b).mp

    rw [← hmEq]
    exact hGood.2

  have hrMem :
      r ∈ ThirtyCoprimeResidueList :=
    mem_thirtyCoprimeResidueList.mpr
      ⟨hrLt, hrCoprime⟩

  rw [mem_goodCoreResidueBlockList]

  exact ⟨r, hrMem, hmEq⟩

/--
The translated residue list is exactly the set of good cores strictly inside
one complete period-30 block.
-/
theorem mem_goodCoreResidueBlockList_iff
    {b m : Nat} :
    m ∈ GoodCoreResidueBlockList b ↔
      30 * b < m ∧
        m < 30 * (b + 1) ∧
        GoodThirtyCore m := by

  constructor
  · exact mem_goodCoreResidueBlockList_data

  · intro hm
    exact
      goodCore_mem_residueBlockList
        hm.1 hm.2.1 hm.2.2

end Erdos536813
