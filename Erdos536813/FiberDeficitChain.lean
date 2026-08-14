import Erdos536813.AxisBound

namespace Erdos536813

/-!
# The high-scale deficit chain for actual 5-adic fiber slices

For a fixed coprime core `m` and outer scale `t`, define

    T_k = floor(t / 5^k),
    q_k = m * 5^k.

A selected slice `F k` lives in the ordinary 2,3-smooth board at scale
`T_k` and corresponds to the ambient fiber with base `q_k`.

The previous files prove the local implication

    T_k ≥ 120  and  d_{k+1} = 0  ==>  d_k ≥ 2,

where

    d_k = L23(T_k) - |F_k|.

This file verifies that the scales and bases line up exactly from one
5-adic layer to the next, and then feeds the local implication into the
abstract `highScaleChain_deficit` theorem.
-/

/-- Scale of the `k`th 5-adic slice. -/
def FiveScale (t k : Nat) : Nat :=
  t / 5 ^ k

/-- Ambient multiplicative base of the `k`th 5-adic slice. -/
def FiveBase (m k : Nat) : Nat :=
  m * 5 ^ k

/-- Actual slice deficit at the `k`th 5-adic layer. -/
def FiberSliceDeficit
    (t : Nat)
    (F : Nat → List Erdos536.GridPoint)
    (k : Nat) : Nat :=
  SliceDeficit (FiveScale t k) (F k)

/-- Adjacent scales differ by division by 5. -/
theorem fiveScale_succ
    (t k : Nat) :
    FiveScale t (k + 1) = FiveScale t k / 5 := by
  unfold FiveScale
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- Adjacent fiber bases differ by multiplication by 5. -/
theorem fiveBase_succ
    (m k : Nat) :
    FiveBase m (k + 1) = 5 * FiveBase m k := by
  simp [FiveBase, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/--
For actual adjacent 5-adic slices, zero upper deficit forces two units of
lower deficit whenever the lower scale is at least 120.
-/
theorem fiveAdic_zero_upper_forces_lower_deficit_two
    {t m N k : Nat}
    {A : List Nat}
    {F : Nat → List Erdos536.GridPoint}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hSelected :
      ∀ r : Nat,
        Erdos536.FiberSelectedComplete
          (F r) A (FiveBase m r))
    (hSub :
      ∀ r : Nat,
        (F r).Subset
          (Erdos536.FiberRegionList 1 (FiveScale t r)))
    (hHigh : 120 ≤ FiveScale t k)
    (hZero : FiberSliceDeficit t F (k + 1) = 0) :
    2 ≤ FiberSliceDeficit t F k := by
  have hq : 0 < FiveBase m k := by
    unfold FiveBase
    exact
      Nat.mul_pos hm
        (Nat.pow_pos (by decide : 0 < (5 : Nat)))

  have hUpperSelected :
      Erdos536.FiberSelectedComplete
        (F (k + 1)) A (5 * FiveBase m k) := by
    simpa [fiveBase_succ] using hSelected (k + 1)

  have hUpperSub :
      (F (k + 1)).Subset
        (FiveInnerBoardList (FiveScale t k)) := by
    apply subset_fiveInnerBoardList_of_subset_div_five
    simpa [fiveScale_succ] using hSub (k + 1)

  have hUpperZero :
      SliceDeficit (FiveScale t k / 5) (F (k + 1)) = 0 := by
    simpa [FiberSliceDeficit, fiveScale_succ] using hZero

  have hLowerSelected :
      Erdos536.FiberSelectedComplete
        (F k) A (FiveBase m k) :=
    hSelected k

  have hLowerBound :
      ∀ p ∈ F k,
        Erdos536.fiberValue 1 p ≤ FiveScale t k := by
    intro p hp
    exact
      (Erdos536.fiberRegionList_complete
        (m := 1) (N := FiveScale t k)
        (by decide : 0 < (1 : Nat)) p).1
        (hSub k hp)

  exact
    zero_upper_deficit_forces_lower_deficit_two_concrete
      hHigh hq hA hUpperSelected hUpperSub hUpperZero
      hLowerSelected hLowerBound

/--
If the first `n` adjacent transitions all occur at scale at least 120, then
the cumulative deficit through layer `n` is at least `n`.
-/
theorem fiveAdic_highScale_prefix_deficit
    {t m N n : Nat}
    {A : List Nat}
    {F : Nat → List Erdos536.GridPoint}
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hSelected :
      ∀ r : Nat,
        Erdos536.FiberSelectedComplete
          (F r) A (FiveBase m r))
    (hSub :
      ∀ r : Nat,
        (F r).Subset
          (Erdos536.FiberRegionList 1 (FiveScale t r)))
    (hHigh :
      ∀ k < n, 120 ≤ FiveScale t k) :
    n ≤ PrefixDeficit (FiberSliceDeficit t F) n := by
  apply highScaleChain_deficit
  intro k hk hZero
  exact
    fiveAdic_zero_upper_forces_lower_deficit_two
      hm hA hSelected hSub (hHigh k hk) hZero

end Erdos536813
