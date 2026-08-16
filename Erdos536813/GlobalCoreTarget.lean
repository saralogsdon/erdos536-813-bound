import Erdos536813.GlobalCoreSum
import Erdos536813.WholeChainTarget

namespace Erdos536813

/-- Sum of the finite target savings over every admissible core. -/
noncomputable def GlobalFiniteTargetSum
    (N : Nat) : Nat :=
  ∑ m ∈ GoodCoreFinset N,
    finiteTargetDeficit (N / m)

/-- Sum of all actual integer-fiber contributions, grouped by core. -/
noncomputable def GlobalCoreIntegerSum
    (A : List Nat)
    (N : Nat) : Nat :=
  ∑ m ∈ GoodCoreFinset N,
    CoreIntegerSum A N m

/-- Sum of the complete-chain baselines over every admissible core. -/
noncomputable def GlobalCoreBaselineSum
    (N : Nat) : Nat :=
  ∑ m ∈ GoodCoreFinset N,
    CoreBaselineSum N m

/--
Summing the finite whole-chain saving over all 30-coprime cores gives
a global target saving.
-/
theorem globalFiniteTarget_add_globalCoreIntegerSum_le_baseline
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    GlobalFiniteTargetSum N +
        GlobalCoreIntegerSum A N
      ≤ GlobalCoreBaselineSum N := by
  unfold GlobalFiniteTargetSum
    GlobalCoreIntegerSum
    GlobalCoreBaselineSum

  rw [← Finset.sum_add_distrib]

  apply Finset.sum_le_sum
  intro m hm

  have hmGood : GoodThirtyCore m :=
    (mem_goodCoreFinset_iff.mp hm).2

  exact
    finiteTarget_plus_coreIntegerSum_le_baseline
      (A := A) (N := N) (m := m)
      hmGood hA

end Erdos536813
