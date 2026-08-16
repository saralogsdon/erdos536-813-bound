import Erdos536813.GlobalBaselineValueMembership

namespace Erdos536813

/-- The explicit axis benchmark contains no repeated grid points. -/
theorem axisBenchmarkList_nodup
    (T : Nat) :
    (AxisBenchmarkList T).Nodup := by

  rw [AxisBenchmarkList, List.nodup_append]

  constructor
  · exact List.nodup_range.map
      (fun i =>
        ({ i := i, j := 0 } : Erdos536.GridPoint))
      (by
        intro a b hab hEq
        exact hab (congrArg Erdos536.GridPoint.i hEq))

  constructor
  · exact List.nodup_range.map
      (fun j =>
        ({ i := 0, j := j + 1 } :
          Erdos536.GridPoint))
      (by
        intro a b hab hEq
        have :
            a + 1 = b + 1 :=
          congrArg Erdos536.GridPoint.j hEq
        exact hab (Nat.add_right_cancel this))

  · apply List.disjoint_left.mpr
    intro p hpLeft hpRight

    rw [List.mem_map] at hpLeft
    rw [List.mem_map] at hpRight

    rcases hpLeft with ⟨i, hi, hLeft⟩
    rcases hpRight with ⟨j, hj, hRight⟩

    have hEq :
        ({ i := i, j := 0 } :
          Erdos536.GridPoint) =
        ({ i := 0, j := j + 1 } :
          Erdos536.GridPoint) := by
      exact hLeft.trans hRight.symm

    have :
        0 = j + 1 :=
      congrArg Erdos536.GridPoint.j hEq

    omega

/-- The list of global baseline pairs contains no duplicates. -/
theorem globalBaselinePairs_nodup
    (N : Nat) :
    (GlobalBaselinePairs N).Nodup := by

  rw [GlobalBaselinePairs]

  change List.Pairwise
    (fun x y : Nat × Erdos536.GridPoint => x ≠ y)
    ((GoodBaseUpToList N).flatMap
      (fun q =>
        (AxisBenchmarkList (N / q)).map
          (fun p => (q, p))))

  rw [List.pairwise_flatMap]

  constructor
  · intro q hq

    exact
      (axisBenchmarkList_nodup (N / q)).map
        (fun p => (q, p))
        (by
          intro p r hpr hEq
          exact hpr (Prod.mk.inj hEq).2)

  · exact List.Pairwise.imp
      (fun {q r} hqr x hx y hy hEq => by
        rw [List.mem_map] at hx
        rw [List.mem_map] at hy

        rcases hx with ⟨p, hp, rfl⟩
        rcases hy with ⟨s, hs, rfl⟩

        exact hqr (Prod.mk.inj hEq).1)
      (goodBaseUpToList_nodup N)

/--
The represented integer value is injective on the global baseline-pair list.
-/
theorem globalBaselinePairValue_injective_on_pairs
    {N : Nat} :
    ∀ qp ∈ GlobalBaselinePairs N,
      ∀ rp ∈ GlobalBaselinePairs N,
        GlobalBaselinePairValue qp =
          GlobalBaselinePairValue rp →
        qp = rp := by

  intro qp hqp rp hrp hValue

  have hqData :=
    mem_globalBaselinePairs.mp hqp

  have hrData :=
    mem_globalBaselinePairs.mp hrp

  have hqGood :
      Erdos536.GoodFiberBase qp.1 :=
    (mem_goodBaseUpToList.mp hqData.1).2

  have hrGood :
      Erdos536.GoodFiberBase rp.1 :=
    (mem_goodBaseUpToList.mp hrData.1).2

  have hFiberValue :
      Erdos536.fiberValue qp.1 qp.2 =
        Erdos536.fiberValue rp.1 rp.2 := by
    simpa [GlobalBaselinePairValue] using hValue

  have hBaseEq :
      qp.1 = rp.1 :=
    Erdos536.fiberValue_base_eq_of_eq_good_bases
      hqGood hrGood hFiberValue

  cases qp with
  | mk q p =>
      cases rp with
      | mk r s =>
          simp at hBaseEq
          cases hBaseEq

          have hPointEq :
              p = s :=
            Erdos536.fiberValue_injective_on_good_base
              hqGood hFiberValue

          cases hPointEq
          rfl

/-- The global baseline value list contains no duplicate integers. -/
theorem globalBaselineValueList_nodup
    {N : Nat} :
    (GlobalBaselineValueList N).Nodup := by

  unfold GlobalBaselineValueList

  apply nodup_map_of_injective_on
    (globalBaselinePairs_nodup N)

  exact globalBaselinePairValue_injective_on_pairs

end Erdos536813
