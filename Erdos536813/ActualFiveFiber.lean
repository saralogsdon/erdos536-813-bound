import Erdos536813.HighScaleDepthSeries

namespace Erdos536813

/-!
# The actual 5-adic fiber chain

The local deficit theorems were stated for an abstract family of slices `F k`.
Here we instantiate that family with the actual selected fibers coming from
the original Erdős 536 set `A`.

For a fixed positive 5-free core `m`, the `k`th base is

    q_k = m * 5^k,

and the normalized scale is

    floor((N / m) / 5^k)
      = floor(N / (m * 5^k)).

Thus the actual selected list

    FiberSelectedList A (m * 5^k) N

lies in exactly the normalized board required by `FiberTarget.lean`.
-/

/-- The actual selected slice at the `k`th 5-adic layer. -/
def ActualFiveSlice
    (A : List Nat)
    (N m k : Nat) :
    List Erdos536.GridPoint :=
  Erdos536.FiberSelectedList A (FiveBase m k) N

/-- Every actual 5-adic slice has the required selected-completeness property. -/
theorem actualFiveSlice_selected
    {A : List Nat}
    {N m : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    ∀ k : Nat,
      Erdos536.FiberSelectedComplete
        (ActualFiveSlice A N m k)
        A
        (FiveBase m k) := by
  intro k
  unfold ActualFiveSlice
  apply Erdos536.fiberSelectedList_complete
  · unfold FiveBase
    exact Nat.mul_pos hm
      (Nat.pow_pos (by decide : 0 < (5 : Nat)))
  · exact hA

/--
The normalized scale used by the 5-adic chain is exactly the ordinary
quotient scale for the actual base `m * 5^k`.
-/
theorem fiveScale_div_base
    (N m k : Nat) :
    FiveScale (N / m) k =
      N / FiveBase m k := by
  unfold FiveScale FiveBase
  rw [Nat.div_div_eq_div_mul]

/--
Each actual selected slice lies in the normalized `2,3`-smooth board at
scale `FiveScale (N / m) k`.
-/
theorem actualFiveSlice_subset_normalized
    {A : List Nat}
    {N m : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    ∀ k : Nat,
      (ActualFiveSlice A N m k).Subset
        (Erdos536.FiberRegionList
          1
          (FiveScale (N / m) k)) := by

  intro k p hp

  have hbase :
      0 < FiveBase m k := by
    unfold FiveBase
    exact Nat.mul_pos hm
      (Nat.pow_pos (by decide : 0 < (5 : Nat)))

  have hSelected :
      Erdos536.FiberSelectedComplete
        (ActualFiveSlice A N m k)
        A
        (FiveBase m k) :=
    actualFiveSlice_selected hm hA k

  have hpA :
      Erdos536.fiberValue (FiveBase m k) p ∈ A :=
    (hSelected.2 p).1 hp

  have hpBound :
      Erdos536.fiberValue (FiveBase m k) p ≤ N :=
    (hA.2.1
      (Erdos536.fiberValue (FiveBase m k) p)
      hpA).2

  have hmul :
      FiveBase m k * Erdos536.fiberValue 1 p ≤ N := by
    simpa [Erdos536.fiberValue, Nat.mul_assoc] using hpBound

  have hnorm :
      Erdos536.fiberValue 1 p ≤
        N / FiveBase m k :=
    (Nat.le_div_iff_mul_le hbase).mpr hmul

  have hscale :
      FiveScale (N / m) k =
        N / FiveBase m k :=
    fiveScale_div_base N m k

  apply
    (Erdos536.fiberRegionList_complete
      (m := 1)
      (N := FiveScale (N / m) k)
      (by decide : 0 < (1 : Nat))
      p).2

  change Erdos536.fiberValue 1 p ≤
    FiveScale (N / m) k

  rw [hscale]
  exact hnorm

/--
The finite target table is therefore realized by the first two slices of the
actual 5-adic chain attached to `A`.
-/
theorem finiteTargetDeficit_le_actualFiveFiber
    {A : List Nat}
    {N m : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    finiteTargetDeficit (N / m) ≤
      PrefixDeficit
        (FiberSliceDeficit
          (N / m)
          (ActualFiveSlice A N m))
        1 := by

  exact
    finiteTargetDeficit_le_fiberPrefix
      hm
      hA
      (actualFiveSlice_selected hm hA)
      (actualFiveSlice_subset_normalized hm hA)

/--
For every actual high-scale fiber, the canonical high target is realized by
the corresponding actual 5-adic deficit prefix.
-/
theorem exists_canonical_highTarget_le_actualFiveFiber
    {A : List Nat}
    {N m : Nat}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (ht : 120 ≤ N / m) :
    ∃ n : Nat,
      1 ≤ n ∧
      24 ≤ FiveScale (N / m) n ∧
      FiveScale (N / m) n ≤ 119 ∧
      highFiberTarget n (FiveScale (N / m) n) ≤
        PrefixDeficit
          (FiberSliceDeficit
            (N / m)
            (ActualFiveSlice A N m))
          (n + 2) := by

  exact
    exists_canonical_highFiberTarget_bound
      ht
      hm
      hA
      (actualFiveSlice_selected hm hA)
      (actualFiveSlice_subset_normalized hm hA)

end Erdos536813
