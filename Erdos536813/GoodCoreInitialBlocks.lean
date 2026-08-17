import Erdos536813.GoodCoreBlockCharacterization

namespace Erdos536813

/--
The concatenation of the first `b` complete period-30 good-core blocks.
-/
def GoodCoreInitialBlockList
    (b : Nat) : List Nat :=
  (List.range b).flatMap
    GoodCoreResidueBlockList

/--
The first `b` complete blocks contain exactly `8*b` entries.
-/
theorem goodCoreInitialBlockList_length
    (b : Nat) :
    (GoodCoreInitialBlockList b).length =
      8 * b := by

  simp [
    GoodCoreInitialBlockList,
    List.length_flatMap,
    goodCoreResidueBlockList_length,
    Nat.mul_comm
  ]

/--
Every entry in the first `b` complete blocks is a positive good core strictly
below `30*b`.
-/
theorem mem_goodCoreInitialBlockList_data
    {b m : Nat}
    (hm : m ∈ GoodCoreInitialBlockList b) :
    0 < m ∧
      m < 30 * b ∧
      GoodThirtyCore m := by

  rw [GoodCoreInitialBlockList, List.mem_flatMap] at hm
  rcases hm with ⟨j, hj, hmBlock⟩

  have hjLt :
      j < b := by
    simpa using hj

  have hmData :=
    mem_goodCoreResidueBlockList_data hmBlock

  have hjSucc :
      j + 1 ≤ b := by
    omega

  have hBlockUpper :
      30 * (j + 1) ≤ 30 * b :=
    Nat.mul_le_mul_left 30 hjSucc

  have hmUpper :
      m < 30 * b :=
    Nat.lt_of_lt_of_le
      hmData.2.1 hBlockUpper

  have hmPos :
      0 < m := by
    exact
      Nat.lt_of_le_of_lt
        (Nat.zero_le (30 * j))
        hmData.1

  exact
    ⟨hmPos, hmUpper, hmData.2.2⟩

/--
In particular, every entry of the initial block list belongs to the global
good-core finset at cutoff `30*b`.
-/
theorem goodCoreInitialBlockList_subset_goodCoreFinset
    {b : Nat} :
    ∀ m ∈ GoodCoreInitialBlockList b,
      m ∈ GoodCoreFinset (30 * b) := by

  intro m hm

  have hmData :=
    mem_goodCoreInitialBlockList_data hm

  apply mem_goodCoreFinset_iff.mpr

  exact
    ⟨Nat.le_of_lt hmData.2.1,
      hmData.2.2⟩

end Erdos536813
