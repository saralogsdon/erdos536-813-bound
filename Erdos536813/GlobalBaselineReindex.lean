import Erdos536813.GlobalCombinedTarget

namespace Erdos536813

/-- The `L23` baseline contribution attached to one five-code. -/
def FiveCodeBaselineWeight
    (N : Nat)
    (p : Nat × Nat) : Nat :=
  L23 (FiveScale (N / p.1) p.2)

/-- The global baseline expressed as a five-code finset sum. -/
noncomputable def GlobalFiveCodeFinsetBaselineSum
    (N : Nat) : Nat :=
  ∑ p ∈ (GoodBaseFiveCodeList N).toFinset,
    FiveCodeBaselineWeight N p

/--
The five-code baseline sum equals the sum of complete baselines over
all good cores.
-/
theorem globalFiveCodeFinsetBaselineSum_eq_globalCoreBaselineSum
    {N : Nat} :
    GlobalFiveCodeFinsetBaselineSum N =
      GlobalCoreBaselineSum N := by
  classical

  unfold GlobalFiveCodeFinsetBaselineSum
    GlobalCoreBaselineSum

  rw [globalCode_toFinset_eq_biUnion_coreDepth]

  rw [Finset.sum_biUnion
    goodCore_pairwise_disjoint_codeImages]

  apply Finset.sum_congr rfl
  intro m hm

  unfold CoreBaselineSum

  rw [Finset.sum_image (by
    intro k₁ hk₁ k₂ hk₂ hEq
    exact congrArg Prod.snd hEq)]

  simp [FiveCodeBaselineWeight]

/--
The noduplicated five-code list baseline equals the corresponding
five-code finset baseline.
-/
theorem fiveCodeBaselineListSum_eq_globalFiveCodeFinsetBaselineSum
    {N : Nat} :
    ((GoodBaseFiveCodeList N).map
      (fun p =>
        L23 (FiveScale (N / p.1) p.2))).sum
      =
    GlobalFiveCodeFinsetBaselineSum N := by
  classical

  have hSum :=
    finsetSum_eq_listMapSum_of_nodup
      (L := GoodBaseFiveCodeList N)
      (f := fun p =>
        L23 (FiveScale (N / p.1) p.2))
      (goodBaseFiveCodeList_nodup N)

  unfold GlobalFiveCodeFinsetBaselineSum
    FiveCodeBaselineWeight

  exact hSum.symm

/--
Consequently, the original five-code list baseline is exactly the global
core baseline.
-/
theorem fiveCodeBaselineListSum_eq_globalCoreBaselineSum
    {N : Nat} :
    ((GoodBaseFiveCodeList N).map
      (fun p =>
        L23 (FiveScale (N / p.1) p.2))).sum
      =
    GlobalCoreBaselineSum N := by

  rw [
    fiveCodeBaselineListSum_eq_globalFiveCodeFinsetBaselineSum,
    globalFiveCodeFinsetBaselineSum_eq_globalCoreBaselineSum
  ]

end Erdos536813
