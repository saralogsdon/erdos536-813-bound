import Erdos536813.FiniteCombinedTargetWeight

namespace Erdos536813

/--
Every outer scale in the factor-five block
`[u * 5^n, (u + 1) * 5^n)` normalizes to `u` at depth `n`.
-/
theorem fiveScale_eq_of_mem_fiveBlock
    {u n t : Nat}
    (ht :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n)) :
    FiveScale t n = u := by

  have htData :
      u * 5 ^ n ≤ t ∧
        t < (u + 1) * 5 ^ n :=
    Finset.mem_Ico.mp ht

  have hPowPos :
      0 < 5 ^ n :=
    Nat.pow_pos (by decide : 0 < (5 : Nat))

  have hLower :
      u ≤ t / 5 ^ n := by
    exact
      (Nat.le_div_iff_mul_le hPowPos).mpr
        htData.1

  have hUpper :
      t / 5 ^ n < u + 1 := by
    exact
      (Nat.div_lt_iff_lt_mul hPowPos).mpr
        htData.2

  unfold FiveScale
  omega

/--
If the terminal scale is at least `24` and the depth is positive, every
outer scale in its factor-five block is at least `120`.
-/
theorem oneTwenty_le_of_mem_fiveBlock
    {u n t : Nat}
    (hu : 24 ≤ u)
    (hn : 1 ≤ n)
    (ht :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n)) :
    120 ≤ t := by

  have htLower :
      u * 5 ^ n ≤ t :=
    (Finset.mem_Ico.mp ht).1

  have hPow :
      5 ≤ 5 ^ n := by
    have h :=
      Nat.pow_le_pow_right
        (by decide : 0 < (5 : Nat))
        hn

    simpa using h

  have hBlockLower :
      120 ≤ u * 5 ^ n := by
    calc
      120 = 24 * 5 := by norm_num
      _ ≤ u * 5 ^ n :=
        Nat.mul_le_mul hu hPow

  exact Nat.le_trans hBlockLower htLower

end Erdos536813
