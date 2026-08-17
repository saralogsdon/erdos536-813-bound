import Erdos536813.GoodCoreDensityLimit

namespace Erdos536813

/--
The good cores `m ≤ N` for which the quotient `N / m` equals `t`.
-/
noncomputable def GoodCoreQuotientFinset
    (N t : Nat) : Finset Nat :=
  (GoodCoreFinset N).filter
    (fun m => N / m = t)

/-- The number of good cores in one quotient fiber. -/
noncomputable def GoodCoreQuotientCount
    (N t : Nat) : Nat :=
  (GoodCoreQuotientFinset N t).card

/-- Membership in a quotient fiber has the expected characterization. -/
theorem mem_goodCoreQuotientFinset_iff
    {N t m : Nat} :
    m ∈ GoodCoreQuotientFinset N t ↔
      m ≤ N ∧
        GoodThirtyCore m ∧
        N / m = t := by

  classical

  simp [
    GoodCoreQuotientFinset,
    mem_goodCoreFinset_iff
  ]

/--
Every quotient arising from a positive good core at most `N` is itself at
most `N`.
-/
theorem quotient_le_of_mem_goodCoreQuotientFinset
    {N t m : Nat}
    (hm : m ∈ GoodCoreQuotientFinset N t) :
    t ≤ N := by

  have hmData :=
    mem_goodCoreQuotientFinset_iff.mp hm

  rw [← hmData.2.2]

  exact Nat.div_le_self N m

/--
Every good core belongs to the quotient fiber indexed by its actual quotient.
-/
theorem mem_own_goodCoreQuotientFinset
    {N m : Nat}
    (hm : m ∈ GoodCoreFinset N) :
    m ∈ GoodCoreQuotientFinset N (N / m) := by

  have hmData :=
    mem_goodCoreFinset_iff.mp hm

  apply mem_goodCoreQuotientFinset_iff.mpr

  exact
    ⟨hmData.1, hmData.2, rfl⟩

/-- Distinct quotient fibers are disjoint. -/
theorem goodCoreQuotientFinset_disjoint
    {N s t : Nat}
    (hst : s ≠ t) :
    Disjoint
      (GoodCoreQuotientFinset N s)
      (GoodCoreQuotientFinset N t) := by

  rw [Finset.disjoint_left]

  intro m hms hmt

  have hs :=
    (mem_goodCoreQuotientFinset_iff.mp hms).2.2

  have ht :=
    (mem_goodCoreQuotientFinset_iff.mp hmt).2.2

  exact hst (hs.symm.trans ht)

end Erdos536813
