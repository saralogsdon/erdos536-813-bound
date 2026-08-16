import Erdos536813.GlobalBaselinePairs

namespace Erdos536813

/--
Membership in the global baseline-pair list is equivalent to having a good
base together with a point in that base's explicit axis benchmark.
-/
theorem mem_globalBaselinePairs
    {N : Nat}
    {qp : Nat × Erdos536.GridPoint} :
    qp ∈ GlobalBaselinePairs N ↔
      qp.1 ∈ GoodBaseUpToList N ∧
      qp.2 ∈ AxisBenchmarkList (N / qp.1) := by

  constructor
  · intro hqp
    rw [GlobalBaselinePairs, List.mem_flatMap] at hqp
    rcases hqp with ⟨q, hq, hp⟩
    rw [List.mem_map] at hp
    rcases hp with ⟨p, hp, hEq⟩
    cases hEq
    exact ⟨hq, hp⟩

  · intro hqp
    rw [GlobalBaselinePairs, List.mem_flatMap]
    exact
      ⟨qp.1, hqp.1,
        List.mem_map_of_mem hqp.2⟩

/--
The integer value represented by a global baseline pair.
-/
def GlobalBaselinePairValue
    (qp : Nat × Erdos536.GridPoint) : Nat :=
  Erdos536.fiberValue qp.1 qp.2

/--
The list of all integer values represented by the global baseline pairs.
-/
def GlobalBaselineValueList
    (N : Nat) : List Nat :=
  (GlobalBaselinePairs N).map GlobalBaselinePairValue

/--
Mapping pairs to their integer values does not change the list length.
-/
theorem globalBaselineValueList_length
    {N : Nat} :
    (GlobalBaselineValueList N).length
      =
    (GlobalBaselinePairs N).length := by

  simp [GlobalBaselineValueList]

/--
Consequently, the global core baseline is exactly the length of the global
baseline value list.
-/
theorem globalBaselineValueList_length_eq_globalCoreBaselineSum
    {N : Nat} :
    (GlobalBaselineValueList N).length
      =
    GlobalCoreBaselineSum N := by

  rw [
    globalBaselineValueList_length,
    globalBaselinePairs_length_eq_globalCoreBaselineSum
  ]

end Erdos536813
