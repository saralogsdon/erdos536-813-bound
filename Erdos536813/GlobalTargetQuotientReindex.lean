import Erdos536813.GoodCoreQuotientFibers

namespace Erdos536813

/--
The quotient fibers indexed by `t ≤ N` have union equal to the entire
good-core finset.
-/
theorem goodCoreFinset_eq_biUnion_quotientFibers
    {N : Nat} :
    GoodCoreFinset N =
      (Finset.range (N + 1)).biUnion
        (GoodCoreQuotientFinset N) := by

  classical

  ext m

  constructor
  · intro hm

    have hmFiber :
        m ∈ GoodCoreQuotientFinset N (N / m) :=
      mem_own_goodCoreQuotientFinset hm

    have hQuotientLe :
        N / m ≤ N :=
      Nat.div_le_self N m

    have hQuotientMem :
        N / m ∈ Finset.range (N + 1) := by
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le hQuotientLe

    apply Finset.mem_biUnion.mpr

    exact
      ⟨N / m, hQuotientMem, hmFiber⟩

  · intro hm

    rcases Finset.mem_biUnion.mp hm with
      ⟨t, ht, hmFiber⟩

    have hmData :=
      mem_goodCoreQuotientFinset_iff.mp hmFiber

    exact
      mem_goodCoreFinset_iff.mpr
        ⟨hmData.1, hmData.2.1⟩

/--
The quotient fibers form a pairwise-disjoint family.
-/
theorem quotientFibers_pairwise_disjoint
    {N : Nat} :
    (↑(Finset.range (N + 1)) : Set Nat).Pairwise
      (fun s t =>
        Disjoint
          (GoodCoreQuotientFinset N s)
          (GoodCoreQuotientFinset N t)) := by

  intro s hs t ht hst

  exact
    goodCoreQuotientFinset_disjoint hst

/--
The global combined target can be reindexed exactly as a sum over quotient
values, weighted by the number of good cores in each quotient fiber.
-/
theorem globalCombinedTargetSum_eq_quotientSum
    (N : Nat) :
    GlobalCombinedTargetSum N =
      ∑ t ∈ Finset.range (N + 1),
        GoodCoreQuotientCount N t *
          CombinedCoreTarget t := by

  classical

  unfold GlobalCombinedTargetSum

  rw [goodCoreFinset_eq_biUnion_quotientFibers]

  rw [
    Finset.sum_biUnion
      quotientFibers_pairwise_disjoint
  ]

  apply Finset.sum_congr rfl
  intro t ht

  calc
    (∑ m ∈ GoodCoreQuotientFinset N t,
        CombinedCoreTarget (N / m))
        =
      ∑ m ∈ GoodCoreQuotientFinset N t,
        CombinedCoreTarget t := by
          apply Finset.sum_congr rfl
          intro m hm

          have hmData :=
            mem_goodCoreQuotientFinset_iff.mp hm

          rw [hmData.2.2]

    _ =
      GoodCoreQuotientCount N t *
        CombinedCoreTarget t := by
          simp [GoodCoreQuotientCount]

end Erdos536813
