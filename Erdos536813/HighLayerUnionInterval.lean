import Erdos536813.HighLayerUnion

namespace Erdos536813

/--
The union of the first `d` complete high layers is exactly the interval
from `120` up to `120 * 5^d`.
-/
theorem highLayerUnion_eq_interval
    (d : Nat) :
    HighLayerUnion d =
      Finset.Ico 120 (120 * 5 ^ d) := by

  ext t
  constructor

  · intro ht

    change
      t ∈
        (Finset.range d).biUnion
          HighLayerInterval at ht

    rcases Finset.mem_biUnion.mp ht with
      ⟨n, hn, htn⟩

    have hnLt :
        n < d :=
      Finset.mem_range.mp hn

    have htnData :
        120 * 5 ^ n ≤ t ∧
          t < 120 * 5 ^ (n + 1) :=
      Finset.mem_Ico.mp htn

    have hLower :
        120 ≤ t :=
      highLayer_scale_ge_120 htn

    have hnSucc :
        n + 1 ≤ d := by
      omega

    have hPow :
        5 ^ (n + 1) ≤ 5 ^ d :=
      Nat.pow_le_pow_right
        (by decide : 0 < (5 : Nat))
        hnSucc

    have hUpperBound :
        120 * 5 ^ (n + 1) ≤
          120 * 5 ^ d :=
      Nat.mul_le_mul_left 120 hPow

    apply Finset.mem_Ico.mpr

    exact
      ⟨hLower,
       htnData.2.trans_le hUpperBound⟩

  · intro ht

    have htData :
        120 ≤ t ∧
          t < 120 * 5 ^ d :=
      Finset.mem_Ico.mp ht

    rcases exists_canonical_block htData.1 with
      ⟨r, u, hrPos, huLower, huUpper,
        hScale, hBlock⟩

    let n : Nat := r - 1

    have hrEq :
        r = n + 1 := by
      dsimp [n]
      omega

    have hnLt :
        n < d := by
      by_contra hNot

      have hdLe :
          d ≤ n :=
        Nat.le_of_not_gt hNot

      have hdLtR :
          d < r := by
        omega

      have hPrefix :
          120 ≤ FiveScale t d :=
        block_high_prefix
          hrPos huLower hBlock d hdLtR

      have hPowPos :
          0 < 5 ^ d :=
        Nat.pow_pos
          (by decide : 0 < (5 : Nat))

      have hLowerMultiple :
          120 * 5 ^ d ≤ t := by
        unfold FiveScale at hPrefix

        exact
          (Nat.le_div_iff_mul_le hPowPos).mp
            hPrefix

      omega

    have hBlockAtN :
        t ∈
          Finset.Ico
            (u * 5 ^ (n + 1))
            ((u + 1) * 5 ^ (n + 1)) := by
      rw [← hrEq]
      exact hBlock

    have htLayer :
        t ∈ HighLayerInterval n :=
      fiveBlock_subset_highLayerInterval
        huLower huUpper hBlockAtN

    unfold HighLayerUnion

    apply Finset.mem_biUnion.mpr

    exact
      ⟨n,
       Finset.mem_range.mpr hnLt,
       htLayer⟩

/--
Thus the expanded high-block weight is an ordinary interval sum.
-/
theorem expandedHighBlockWeight_eq_interval_sum
    (d : Nat) :
    ExpandedHighBlockWeight d =
      ∑ t ∈ Finset.Ico 120 (120 * 5 ^ d),
        (combinedTargetWeight t : ℝ) := by

  rw [
    expandedHighBlockWeight_eq_highLayerUnion_sum,
    highLayerUnion_eq_interval
  ]

end Erdos536813
