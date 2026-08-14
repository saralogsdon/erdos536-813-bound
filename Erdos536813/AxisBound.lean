import Erdos536813.ZeroUpperBridge

namespace Erdos536813

/-!
# The ordinary one-slice `L23` bound

Kenta's lattice projection theorem says that a Gamma-free family in a
downward-closed board has cardinality at most the number of axis points.

For the 2,3-smooth board at scale `T`, every axis point is one of

    (i, 0),  0 ≤ i ≤ log_2 T,

or

    (0, j),  1 ≤ j ≤ log_3 T.

We package these points into an explicit benchmark list of length exactly

    log_2 T + log_3 T + 1 = L23 T.

This closes the last generic hypothesis in the zero-upper-deficit bridge.
-/

/-- Explicit list containing every coordinate-axis point in the scale-`T` board. -/
def AxisBenchmarkList (T : Nat) : List Erdos536.GridPoint :=
  (List.range (Nat.log 2 T + 1)).map
      (fun i => ({ i := i, j := 0 } : Erdos536.GridPoint)) ++
    (List.range (Nat.log 3 T)).map
      (fun j => ({ i := 0, j := j + 1 } : Erdos536.GridPoint))

/-- The explicit axis benchmark has exactly `L23 T` entries. -/
theorem axisBenchmarkList_length
    (T : Nat) :
    (AxisBenchmarkList T).length = L23 T := by
  simp [AxisBenchmarkList, L23]
  omega

/-- Every axis point in the ordinary 2,3-smooth board lies in the benchmark list. -/
theorem axis_mem_axisBenchmarkList
    {T : Nat}
    {p : Erdos536.GridPoint}
    (hpRegion : p ∈ Erdos536.FiberRegionList 1 T)
    (hAxis : Erdos536.GridPoint.axis p) :
    p ∈ AxisBenchmarkList T := by
  have hpBound : Erdos536.fiberValue 1 p ≤ T :=
    (Erdos536.fiberRegionList_complete
      (m := 1) (N := T)
      (by decide : 0 < (1 : Nat)) p).1 hpRegion

  rcases p with ⟨i, j⟩
  change i = 0 ∨ j = 0 at hAxis
  rcases hAxis with hi | hj
  · subst i
    by_cases hj0 : j = 0
    · subst j
      apply List.mem_append.mpr
      left
      apply List.mem_map.mpr
      refine ⟨0, ?_, rfl⟩
      simp
    · have hPow : 3 ^ j ≤ T := by
        simpa [Erdos536.fiberValue] using hpBound
      have hjle : j ≤ Nat.log 3 T :=
        Nat.le_log_of_pow_le (by decide : 1 < (3 : Nat)) hPow
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hpred : j - 1 < Nat.log 3 T := by
        omega
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      refine ⟨j - 1, List.mem_range.mpr hpred, ?_⟩
      have hEq : j - 1 + 1 = j :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)
      simp [hEq]
  · subst j
    have hPow : 2 ^ i ≤ T := by
      simpa [Erdos536.fiberValue] using hpBound
    have hile : i ≤ Nat.log 2 T :=
      Nat.le_log_of_pow_le (by decide : 1 < (2 : Nat)) hPow
    apply List.mem_append.mpr
    left
    apply List.mem_map.mpr
    refine ⟨i, List.mem_range.mpr ?_, rfl⟩
    omega

/--
The axis part of the ordinary scale-`T` fiber region has at most `L23 T`
points.
-/
theorem fiberRegion_axis_card_le_L23
    (T : Nat) :
    ((Erdos536.FiberRegionList 1 T).filter
      Erdos536.GridPoint.axisBool).length ≤ L23 T := by
  let Axis :=
    (Erdos536.FiberRegionList 1 T).filter
      Erdos536.GridPoint.axisBool

  have hAxisNodup : Axis.Nodup := by
    dsimp [Axis]
    exact
      (Erdos536.fiberRegionList_nodup 1 T).filter
        Erdos536.GridPoint.axisBool

  have hAxisSub : Axis.Subset (AxisBenchmarkList T) := by
    intro p hp
    have hpData :
        p ∈ Erdos536.FiberRegionList 1 T ∧
          Erdos536.GridPoint.axisBool p = true := by
      simpa [Axis] using (List.mem_filter.mp hp)

    have hAxisProp : Erdos536.GridPoint.axis p := by
      rcases p with ⟨i, j⟩
      simp [Erdos536.GridPoint.axisBool, Erdos536.GridPoint.axis] at hpData ⊢
      exact hpData.2

    exact axis_mem_axisBenchmarkList hpData.1 hAxisProp

  have hFinsetSub :
      Axis.toFinset ⊆ (AxisBenchmarkList T).toFinset := by
    intro p hp
    have hpAxis : p ∈ Axis := by
      simpa using hp
    have hpBench : p ∈ AxisBenchmarkList T :=
      hAxisSub hpAxis
    simpa using hpBench

  have hCard :
      Axis.toFinset.card ≤ (AxisBenchmarkList T).toFinset.card :=
    Finset.card_le_card hFinsetSub

  calc
    ((Erdos536.FiberRegionList 1 T).filter
        Erdos536.GridPoint.axisBool).length
        = Axis.length := by rfl
    _ = Axis.toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup hAxisNodup
    _ ≤ (AxisBenchmarkList T).toFinset.card := hCard
    _ ≤ (AxisBenchmarkList T).length :=
      List.toFinset_card_le
    _ = L23 T := axisBenchmarkList_length T

/--
The ordinary one-slice Gamma-free bound in the exact form needed by the
5-adic deficit argument.
-/
theorem gammaFree_fiberRegion_card_le_L23
    {T : Nat}
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (Erdos536.FiberRegionList 1 T)) :
    S.length ≤ L23 T := by
  have hDown :
      Erdos536.DownClosed (Erdos536.FiberRegionList 1 T) :=
    Erdos536.fiberRegionComplete_downClosed
      (Erdos536.fiberRegionList_complete
        (m := 1) (N := T)
        (by decide : 0 < (1 : Nat)))

  have hProjection :
      S.length ≤
        ((Erdos536.FiberRegionList 1 T).filter
          Erdos536.GridPoint.axisBool).length :=
    Erdos536.gammaFree_card_le_axis_card
      hSub hDown hGamma

  exact Nat.le_trans hProjection (fiberRegion_axis_card_le_L23 T)

/-- The same one-slice bound on the adjacent upper inner board. -/
theorem gammaFree_fiveInnerBoard_card_le_L23
    {T : Nat}
    {U : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree U)
    (hSub : U.Subset (FiveInnerBoardList T)) :
    U.length ≤ L23 (T / 5) := by
  exact
    gammaFree_fiberRegion_card_le_L23
      hGamma
      (subset_div_five_of_subset_fiveInnerBoardList hSub)

/--
Concrete adjacent-layer deficit implication with no abstract cardinality
hypothesis remaining.
-/
theorem zero_upper_deficit_forces_lower_deficit_two_concrete
    {T q N : Nat}
    {A : List Nat}
    {Upper Lower : List Erdos536.GridPoint}
    (hT : 120 ≤ T)
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete Upper A (5 * q))
    (hUpperSub :
      Upper.Subset (FiveInnerBoardList T))
    (hUpperZero :
      SliceDeficit (T / 5) Upper = 0)
    (hLowerSelected :
      Erdos536.FiberSelectedComplete Lower A q)
    (hLowerBound :
      ∀ p ∈ Lower, Erdos536.fiberValue 1 p ≤ T) :
    2 ≤ SliceDeficit T Lower := by
  exact
    zero_upper_deficit_forces_lower_deficit_two
      hT hq hA hUpperSelected hUpperSub
      (fun U hGamma hSub =>
        gammaFree_fiveInnerBoard_card_le_L23 hGamma hSub)
      hUpperZero hLowerSelected hLowerBound

end Erdos536813
