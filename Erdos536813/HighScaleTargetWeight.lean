import Erdos536813.FiveBlockDecomposition
import Erdos536813.HighScaleBlockWeight

namespace Erdos536813

/-!
# Weighted high-scale targets at fixed 5-adic depth

The previous files establish two independent facts:

* `highFiberTarget n u` is the deficit forced in a fiber whose canonical
  terminal scale is `u` at depth `n`;
* a complete `(n,u)` factor-5 block has outer weight
  `5^{-n} * uWeight u`.

This file combines those ingredients and sums over the terminal window
`24..119`.

At fixed depth `n`, the weighted target is

    (n / 5^n) * (1/30) + (1 / 5^n) * (1/75),

which is exactly the summand whose depth sums give `1/96` and `1/300`.
-/

/--
A rational-valued version of the high-scale target times the terminal
`u`-weight.
-/
def highTargetUWeight (n u : Nat) : ℚ :=
  (n : ℚ) * uWeight u +
    if InHighExtraRange u then uWeight u else 0

/--
`highTargetUWeight` is exactly the natural-valued `highFiberTarget`, cast to
`ℚ`, times `uWeight`.
-/
theorem highTargetUWeight_eq
    (n u : Nat) :
    highTargetUWeight n u =
      (highFiberTarget n u : ℚ) * uWeight u := by
  unfold highTargetUWeight highFiberTarget
  by_cases h : InHighExtraRange u <;>
    simp [h] <;>
    ring

/--
The extra terminal indicator contributes exactly `1/75` across `24..119`.
This is the indicator-form version of `extra_u_weight_sum`.
-/
theorem highExtra_indicator_u_weight_sum :
    (∑ u ∈ Finset.Icc 24 119,
      if InHighExtraRange u then uWeight u else 0) =
        (1 / 75 : ℚ) := by
  native_decide

/--
At fixed depth `n`, before inserting the factor `5^{-n}`, the total target
over all terminal scales is `n/30 + 1/75`.
-/
theorem highTarget_u_weight_sum
    (n : Nat) :
    (∑ u ∈ Finset.Icc 24 119, highTargetUWeight n u) =
      (n : ℚ) * (1 / 30) + 1 / 75 := by
  unfold highTargetUWeight
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [base_u_weight_sum]
  rw [highExtra_indicator_u_weight_sum]

/--
For one complete `(n,u)` block, multiplying its outer weight by the forced
target gives exactly `5^{-n} * highTargetUWeight n u`.
-/
theorem fiveBlock_highTarget_weight
    {n u : Nat}
    (hu : 0 < u) :
    (highFiberTarget n u : ℚ) *
        (∑ t ∈
          Finset.Ico
            (u * 5 ^ n)
            ((u + 1) * 5 ^ n),
          outerWeight t) =
      (1 / (((5 ^ n : Nat) : ℚ))) *
        highTargetUWeight n u := by
  rw [fiveBlock_outerWeight_sum hu]
  rw [highTargetUWeight_eq]
  ring

/--
Summing all terminal blocks at fixed depth `n` gives the precise base-plus-
bonus expression used by the geometric bookkeeping.
-/
theorem fixedDepth_highTarget_weight_sum
    (n : Nat) :
    (∑ u ∈ Finset.Icc 24 119,
      (1 / (((5 ^ n : Nat) : ℚ))) *
        highTargetUWeight n u) =
      (n : ℚ) * (1 / (((5 ^ n : Nat) : ℚ))) * (1 / 30) +
        (1 / (((5 ^ n : Nat) : ℚ))) * (1 / 75) := by
  rw [← Finset.mul_sum]
  rw [highTarget_u_weight_sum]
  ring

end Erdos536813
