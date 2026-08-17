import Erdos536813.GoodCoreInitialBlocks

namespace Erdos536813

/--
Distinct period-30 blocks are disjoint.
-/
theorem goodCoreResidueBlocks_disjoint
    {j k : Nat}
    (hjk : j ≠ k) :
    (GoodCoreResidueBlockList j).Disjoint
      (GoodCoreResidueBlockList k) := by

  apply List.disjoint_left.mpr
  intro m hmj hmk

  have hjData :=
    mem_goodCoreResidueBlockList_data hmj

  have hkData :=
    mem_goodCoreResidueBlockList_data hmk

  rcases Nat.lt_or_gt_of_ne hjk with hjkLt | hkjLt

  · have hBlocks :
        30 * (j + 1) ≤ 30 * k := by
      exact
        Nat.mul_le_mul_left 30
          (Nat.succ_le_of_lt hjkLt)

    have :
        m < m := by
      exact Nat.lt_of_lt_of_le
        hjData.2.1
        (Nat.le_trans hBlocks
          (Nat.le_of_lt hkData.1))

    exact Nat.lt_irrefl m this

  · have hBlocks :
        30 * (k + 1) ≤ 30 * j := by
      exact
        Nat.mul_le_mul_left 30
          (Nat.succ_le_of_lt hkjLt)

    have :
        m < m := by
      exact Nat.lt_of_lt_of_le
        hkData.2.1
        (Nat.le_trans hBlocks
          (Nat.le_of_lt hjData.1))

    exact Nat.lt_irrefl m this

/--
The concatenation of the first `b` complete blocks contains no duplicates.
-/
theorem goodCoreInitialBlockList_nodup
    (b : Nat) :
    (GoodCoreInitialBlockList b).Nodup := by

  rw [GoodCoreInitialBlockList]

  change List.Pairwise
    (fun x y : Nat => x ≠ y)
    ((List.range b).flatMap
      GoodCoreResidueBlockList)

  rw [List.pairwise_flatMap]

  constructor
  · intro j hj
    exact goodCoreResidueBlockList_nodup j

  · exact List.Pairwise.imp
      (fun {j k} hjk x hx y hy hEq => by
        exact
          (List.disjoint_left.mp
            (goodCoreResidueBlocks_disjoint hjk)
            hx hy)
            hEq)
      List.nodup_range

/--
The first `b` complete blocks give at least `8*b` good cores below `30*b`.
-/
theorem eight_mul_le_goodCoreFinset_card
    (b : Nat) :
    8 * b ≤
      (GoodCoreFinset (30 * b)).card := by

  have hNodup :
      (GoodCoreInitialBlockList b).Nodup :=
    goodCoreInitialBlockList_nodup b

  have hSubset :
      (GoodCoreInitialBlockList b).toFinset ⊆
        GoodCoreFinset (30 * b) := by
    intro m hm

    have hmList :
        m ∈ GoodCoreInitialBlockList b := by
      simpa using hm

    exact
      goodCoreInitialBlockList_subset_goodCoreFinset
        m hmList

  calc
    8 * b =
        (GoodCoreInitialBlockList b).length := by
          symm
          exact goodCoreInitialBlockList_length b

    _ =
        (GoodCoreInitialBlockList b).toFinset.card := by
          symm
          exact List.toFinset_card_of_nodup hNodup

    _ ≤
        (GoodCoreFinset (30 * b)).card :=
      Finset.card_le_card hSubset

end Erdos536813
