import Erdos536813.GlobalCoreDisjoint

namespace Erdos536813

/-- The actual integer-fiber contribution attached to a five-code. -/
noncomputable def FiveCodeIntegerWeight
    (A : List Nat)
    (p : Nat × Nat) : Nat :=
  (Erdos536.FiberIntegerList A
    (FiveBase p.1 p.2)).length

/--
The original five-code contribution, expressed as a finset sum.
-/
noncomputable def GlobalFiveCodeFinsetIntegerSum
    (A : List Nat)
    (N : Nat) : Nat :=
  ∑ p ∈ (GoodBaseFiveCodeList N).toFinset,
    FiveCodeIntegerWeight A p

/--
The global five-code finset sum is exactly the sum of the complete
integer-fiber chains over all good cores.
-/
theorem globalFiveCodeFinsetIntegerSum_eq_globalCoreIntegerSum
    {A : List Nat}
    {N : Nat} :
    GlobalFiveCodeFinsetIntegerSum A N =
      GlobalCoreIntegerSum A N := by
  classical

  unfold GlobalFiveCodeFinsetIntegerSum
    GlobalCoreIntegerSum

  rw [globalCode_toFinset_eq_biUnion_coreDepth]

  rw [Finset.sum_biUnion
    goodCore_pairwise_disjoint_codeImages]

  apply Finset.sum_congr rfl
  intro m hm

  unfold CoreIntegerSum

  rw [Finset.sum_image (by
    intro k₁ hk₁ k₂ hk₂ hEq
    exact (Prod.mk.inj_iff.mp hEq).2)]

  simp [FiveCodeIntegerWeight]

end Erdos536813
