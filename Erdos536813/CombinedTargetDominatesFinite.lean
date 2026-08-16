import Erdos536813.GlobalBaselineBound

namespace Erdos536813

/--
Below scale `120`, the combined target is exactly the finite target deficit.
-/
theorem combinedCoreTarget_eq_finiteTargetDeficit_of_lt
    {t : Nat}
    (ht : t < 120) :
    CombinedCoreTarget t =
      finiteTargetDeficit t := by

  simp [CombinedCoreTarget, Nat.not_le.mpr ht]

/--
At every scale, the combined target is at least the finite target deficit.
For high scales the finite target is zero; for low scales the two targets
are equal.
-/
theorem finiteTargetDeficit_le_combinedCoreTarget
    (t : Nat) :
    finiteTargetDeficit t ≤
      CombinedCoreTarget t := by

  by_cases ht : 120 ≤ t

  · have hFinite :
        finiteTargetDeficit t = 0 := by
      unfold finiteTargetDeficit
      split
      · rename_i hTwo
        rcases hTwo with hRange | hRange <;> omega
      · split
        · rename_i hOne
          rcases hOne with hRange | hRange
          · rcases hRange with hRange | hRange
            · rcases hRange with hRange | hRange <;> omega
            · omega
          · omega
        · rfl

    rw [hFinite]
    exact Nat.zero_le _

  · have htlt : t < 120 :=
      Nat.lt_of_not_ge ht

    rw [
      combinedCoreTarget_eq_finiteTargetDeficit_of_lt
        htlt
    ]

/--
Summing over every good core, the global combined target dominates the
previously defined global finite target.
-/
theorem globalFiniteTargetSum_le_globalCombinedTargetSum
    (N : Nat) :
    GlobalFiniteTargetSum N ≤
      GlobalCombinedTargetSum N := by

  unfold GlobalFiniteTargetSum
    GlobalCombinedTargetSum

  apply Finset.sum_le_sum
  intro m hm

  exact
    finiteTargetDeficit_le_combinedCoreTarget
      (N / m)

end Erdos536813
