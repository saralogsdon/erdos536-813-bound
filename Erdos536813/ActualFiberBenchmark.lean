import Erdos536813.ActualFiveFiber

namespace Erdos536813

/-!
# Actual fiber counts versus the L23 benchmark

This file converts the slice deficits into a direct improvement of the
original fiber-counting argument.

For the actual selected slice at base `m * 5^k` we prove

    |FiberIntegerList A (m * 5^k)|
      + FiberSliceDeficit ...
      ≤ L23 (FiveScale (N / m) k).

Summing over a prefix of 5-adic layers then gives

    actual integer count + cumulative deficit ≤ cumulative L23 baseline.

This is the bridge needed to subtract the finite/high target deficits from
the same fiber count used in the original `5/6` proof.
-/

/-- The actual selected slice is Gamma-free. -/
theorem actualFiveSlice_gammaFree
    {A : List Nat}
    {N m k : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    Erdos536.GammaFree
      (ActualFiveSlice A N m k) := by

  have hbase :
      0 < FiveBase m k := by
    unfold FiveBase
    exact Nat.mul_pos hm
      (Nat.pow_pos (by decide : 0 < (5 : Nat)))

  exact
    Erdos536.fiberSelected_gammaFree
      hbase
      hA
      (actualFiveSlice_selected hm hA k)

/-- Every actual selected slice lies below the ordinary `L23` benchmark. -/
theorem actualFiveSlice_length_le_L23
    {A : List Nat}
    {N m k : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    (ActualFiveSlice A N m k).length ≤
      L23 (FiveScale (N / m) k) := by

  exact
    gammaFree_fiberRegion_card_le_L23
      (actualFiveSlice_gammaFree hm hA)
      (actualFiveSlice_subset_normalized hm hA k)

/--
For an actual slice, selected cardinality plus its numerical deficit is
exactly the `L23` benchmark.
-/
theorem actualFiveSlice_length_add_deficit
    {A : List Nat}
    {N m k : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    (ActualFiveSlice A N m k).length +
        FiberSliceDeficit
          (N / m)
          (ActualFiveSlice A N m)
          k =
      L23 (FiveScale (N / m) k) := by

  have hcap :=
    actualFiveSlice_length_le_L23
      (A := A) (N := N) (m := m) (k := k)
      hm hA

  unfold FiberSliceDeficit SliceDeficit
  omega

/--
The original integer fiber used in the upstream `5/6` proof injects into the
actual selected lattice slice.
-/
theorem fiberIntegerList_length_le_actualFiveSlice
    {A : List Nat}
    {N m k : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    (Erdos536.FiberIntegerList A (FiveBase m k)).length ≤
      (ActualFiveSlice A N m k).length := by

  simpa [ActualFiveSlice] using
    (Erdos536.fiberIntegerList_card_le_selectedList_card
      (A := A)
      (N := N)
      (m := FiveBase m k)
      hA)

/--
Hence the upstream integer-fiber cardinality plus our actual slice deficit
is bounded by the same `L23` benchmark.
-/
theorem fiberIntegerList_add_actual_deficit_le_L23
    {A : List Nat}
    {N m k : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    (Erdos536.FiberIntegerList A (FiveBase m k)).length +
        FiberSliceDeficit
          (N / m)
          (ActualFiveSlice A N m)
          k ≤
      L23 (FiveScale (N / m) k) := by

  have hInt :=
    fiberIntegerList_length_le_actualFiveSlice
      (A := A) (N := N) (m := m) (k := k)
      hA

  have hEq :=
    actualFiveSlice_length_add_deficit
      (A := A) (N := N) (m := m) (k := k)
      hm hA

  omega

/-- Integer-fiber count through the `r`th 5-adic layer. -/
noncomputable def ActualFiveIntegerPrefix
    (A : List Nat)
    (N m r : Nat) : Nat :=
  ∑ k ∈ Finset.range (r + 1),
    (Erdos536.FiberIntegerList A (FiveBase m k)).length

/-- `L23` baseline through the `r`th 5-adic layer. -/
def FiveBaselinePrefix
    (N m r : Nat) : Nat :=
  ∑ k ∈ Finset.range (r + 1),
    L23 (FiveScale (N / m) k)

/--
Summing the pointwise identity gives the key prefix inequality:
integer count plus cumulative actual deficit is at most the cumulative
`L23` baseline.
-/
theorem actualFiveIntegerPrefix_add_deficit_le_baseline
    {A : List Nat}
    {N m r : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    ActualFiveIntegerPrefix A N m r +
        PrefixDeficit
          (FiberSliceDeficit
            (N / m)
            (ActualFiveSlice A N m))
          r ≤
      FiveBaselinePrefix N m r := by

  unfold ActualFiveIntegerPrefix FiveBaselinePrefix PrefixDeficit
  rw [← Finset.sum_add_distrib]

  apply Finset.sum_le_sum
  intro k hk

  exact
    fiberIntegerList_add_actual_deficit_le_L23
      (A := A) (N := N) (m := m) (k := k)
      hm hA

/--
The finite target therefore subtracts directly from the upstream integer
count on the first two 5-adic layers.
-/
theorem finiteTarget_plus_actualFiveIntegerPrefix_le_baseline
    {A : List Nat}
    {N m : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    finiteTargetDeficit (N / m) +
        ActualFiveIntegerPrefix A N m 1 ≤
      FiveBaselinePrefix N m 1 := by

  have hTarget :=
    finiteTargetDeficit_le_actualFiveFiber
      (A := A) (N := N) (m := m)
      hm hA

  have hPrefix :=
    actualFiveIntegerPrefix_add_deficit_le_baseline
      (A := A) (N := N) (m := m) (r := 1)
      hm hA

  omega

/--
At high scale, the canonical target likewise subtracts directly from the
upstream integer-fiber count through the prefix used by the combinatorial
proof.
-/
theorem exists_canonical_highTarget_plus_actualFiveIntegerPrefix_le_baseline
    {A : List Nat}
    {N m : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (ht : 120 ≤ N / m) :
    ∃ n : Nat,
      1 ≤ n ∧
      24 ≤ FiveScale (N / m) n ∧
      FiveScale (N / m) n ≤ 119 ∧
      highFiberTarget n (FiveScale (N / m) n) +
          ActualFiveIntegerPrefix A N m (n + 2) ≤
        FiveBaselinePrefix N m (n + 2) := by

  rcases
    exists_canonical_highTarget_le_actualFiveFiber
      (A := A) (N := N) (m := m)
      hm hA ht
    with
      ⟨n, hn, hLower, hUpper, hTarget⟩

  have hPrefix :=
    actualFiveIntegerPrefix_add_deficit_le_baseline
      (A := A) (N := N) (m := m) (r := n + 2)
      hm hA

  refine ⟨n, hn, hLower, hUpper, ?_⟩
  omega

end Erdos536813
