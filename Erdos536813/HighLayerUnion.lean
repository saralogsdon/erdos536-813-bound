import Erdos536813.HighLayerPartition

namespace Erdos536813

/-- The union of the first `d` complete positive-depth high layers. -/
def HighLayerUnion
    (d : Nat) : Finset Nat :=
  (Finset.range d).biUnion HighLayerInterval

/-- Distinct complete high layers are disjoint. -/
theorem highLayerIntervals_disjoint
    {n₁ n₂ : Nat}
    (hne : n₁ ≠ n₂) :
    Disjoint
      (HighLayerInterval n₁)
      (HighLayerInterval n₂) := by

  rw [Finset.disjoint_left]
  intro t ht₁ ht₂

  have htUnion₁ :
      t ∈ HighLayerBlockUnion n₁ := by
    rw [highLayerBlockUnion_eq n₁]
    exact ht₁

  have htUnion₂ :
      t ∈ HighLayerBlockUnion n₂ := by
    rw [highLayerBlockUnion_eq n₂]
    exact ht₂

  rcases Finset.mem_biUnion.mp htUnion₁ with
    ⟨u₁, hu₁, hBlock₁⟩

  rcases Finset.mem_biUnion.mp htUnion₂ with
    ⟨u₂, hu₂, hBlock₂⟩

  have hu₁Data :
      24 ≤ u₁ ∧ u₁ ≤ 119 :=
    Finset.mem_Icc.mp hu₁

  have hu₂Data :
      24 ≤ u₂ ∧ u₂ ≤ 119 :=
    Finset.mem_Icc.mp hu₂

  have hUnique :=
    canonical_block_unique
      (t := t)
      (n := n₁ + 1)
      (u := u₁)
      (n' := n₂ + 1)
      (u' := u₂)
      (by omega)
      (by omega)
      hu₁Data.1
      hu₁Data.2
      hu₂Data.1
      hu₂Data.2
      hBlock₁
      hBlock₂

  apply hne
  omega

/--
The first `d` complete high layers form a pairwise-disjoint family.
-/
theorem highLayerIntervals_pairwise_disjoint
    (d : Nat) :
    (↑(Finset.range d) : Set Nat).Pairwise
      (fun n₁ n₂ =>
        Disjoint
          (HighLayerInterval n₁)
          (HighLayerInterval n₂)) := by

  intro n₁ hn₁ n₂ hn₂ hne

  exact highLayerIntervals_disjoint hne

/--
A sum over the union of the first `d` high layers separates into the
corresponding sum over individual layers.
-/
theorem highLayerUnion_combinedTargetWeight_sum
    (d : Nat) :
    (∑ t ∈ HighLayerUnion d,
      (combinedTargetWeight t : ℝ))
      =
    ∑ n ∈ Finset.range d,
      ∑ t ∈ HighLayerInterval n,
        (combinedTargetWeight t : ℝ) := by

  unfold HighLayerUnion

  rw [
    Finset.sum_biUnion
      (highLayerIntervals_pairwise_disjoint d)
  ]

/--
The expanded high-block weight is exactly the combined target weight
summed over the disjoint union of the first `d` high layers.
-/
theorem expandedHighBlockWeight_eq_highLayerUnion_sum
    (d : Nat) :
    ExpandedHighBlockWeight d =
      ∑ t ∈ HighLayerUnion d,
        (combinedTargetWeight t : ℝ) := by

  rw [highLayerUnion_combinedTargetWeight_sum]

  unfold ExpandedHighBlockWeight

  apply Finset.sum_congr rfl
  intro n hn

  exact
    (highLayer_combinedTargetWeight_sum n).symm

end Erdos536813
