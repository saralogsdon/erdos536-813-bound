import Erdos536813.HighScaleGeometric

namespace Erdos536813

/-!
# Exact weights of canonical factor-5 blocks

For the outer scale `t`, the asymptotic fiber-counting weight is

    1 / (t (t + 1)).

For a fixed terminal scale `u` and 5-adic depth `n`, the scales belonging to
that block are

    u * 5^n ≤ t < (u + 1) * 5^n.

The reciprocal weight telescopes across this interval, giving exactly

    (1 / 5^n) * (1 / (u (u + 1))).

This is the finite arithmetic bridge between the canonical factor-5
decomposition and the geometric-series bookkeeping.
-/

/-- The outer-scale weight used in the global fiber sum. -/
def outerWeight (t : Nat) : ℚ :=
  1 / ((t : ℚ) * ((t + 1 : Nat) : ℚ))

/-- One outer weight is a telescoping difference of reciprocals. -/
theorem outerWeight_eq_telescoping
    {t : Nat}
    (ht : 0 < t) :
    outerWeight t =
      (-(1 / (((t + 1 : Nat) : ℚ)))) -
        (-(1 / (t : ℚ))) := by
  have htq : (t : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ht)
  have hsuccq : ((t + 1 : Nat) : ℚ) ≠ 0 := by
    positivity
  unfold outerWeight
  push_cast
  field_simp [htq, hsuccq]
  ring

/--
The weights telescope on every positive integer interval `[a,b)`.
-/
theorem sum_outerWeight_Ico
    {a b : Nat}
    (ha : 0 < a)
    (hab : a ≤ b) :
    (∑ t ∈ Finset.Ico a b, outerWeight t) =
      1 / (a : ℚ) - 1 / (b : ℚ) := by
  calc
    (∑ t ∈ Finset.Ico a b, outerWeight t) =
        ∑ t ∈ Finset.Ico a b,
          ((fun k : Nat => -(1 / (k : ℚ))) (t + 1) -
            (fun k : Nat => -(1 / (k : ℚ))) t) := by
      apply Finset.sum_congr rfl
      intro t htmem
      have hat : a ≤ t :=
        (Finset.mem_Ico.mp htmem).1
      exact
        outerWeight_eq_telescoping
          (lt_of_lt_of_le ha hat)
    _ =
        (-(1 / (b : ℚ))) -
          (-(1 / (a : ℚ))) := by
      simpa using
        (Finset.sum_Ico_sub
          (fun k : Nat => -(1 / (k : ℚ))) hab)
    _ = 1 / (a : ℚ) - 1 / (b : ℚ) := by
      ring

/--
A complete factor-5 block has weight `5^{-n} * uWeight u`.
-/
theorem fiveBlock_outerWeight_sum
    {u n : Nat}
    (hu : 0 < u) :
    (∑ t ∈
        Finset.Ico
          (u * 5 ^ n)
          ((u + 1) * 5 ^ n),
        outerWeight t) =
      (1 / (((5 ^ n : Nat) : ℚ))) * uWeight u := by
  have hpow : 0 < 5 ^ n :=
    Nat.pow_pos (by decide : 0 < (5 : Nat))
  have hstart : 0 < u * 5 ^ n :=
    Nat.mul_pos hu hpow
  have hle :
      u * 5 ^ n ≤ (u + 1) * 5 ^ n := by
    exact Nat.mul_le_mul_right (5 ^ n) (Nat.le_succ u)

  rw [sum_outerWeight_Ico hstart hle]
  unfold uWeight
  push_cast

  have huq : (u : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hu)
  have hpowq : ((5 : ℚ) ^ n) ≠ 0 :=
    pow_ne_zero n (by norm_num : (5 : ℚ) ≠ 0)

  field_simp [huq, hpowq]
  ring

end Erdos536813
