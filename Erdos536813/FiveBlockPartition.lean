import Erdos536813.HighScaleTargetWeight

namespace Erdos536813

/-!
# Exact interval description of factor-5 blocks

The canonical high-scale argument uses

    FiveScale t n = t / 5^n.

The weighted bookkeeping, on the other hand, sums over the integer block

    u * 5^n ≤ t < (u + 1) * 5^n.

This file proves that these are exactly the same condition.  It is the
structural bridge that lets us replace a sum over outer scales `t` by sums
over canonical depth/terminal pairs `(n,u)`.
-/

/--
`FiveScale t n = u` iff `t` lies in the complete factor-5 block associated
to depth `n` and terminal scale `u`.
-/
theorem fiveScale_eq_iff_block
    {t n u : Nat} :
    FiveScale t n = u ↔
      u * 5 ^ n ≤ t ∧
      t < (u + 1) * 5 ^ n := by
  unfold FiveScale
  have hpow : 0 < 5 ^ n :=
    Nat.pow_pos (by decide : 0 < (5 : Nat))

  constructor

  · intro hEq
    have hLowerDiv : u ≤ t / 5 ^ n := by
      rw [hEq]

    have hUpperDiv : t / 5 ^ n < u + 1 := by
      rw [hEq]
      omega

    exact
      ⟨(Nat.le_div_iff_mul_le hpow).mp hLowerDiv,
       (Nat.div_lt_iff_lt_mul hpow).mp hUpperDiv⟩

  · rintro ⟨hLower, hUpper⟩

    have hLowerDiv : u ≤ t / 5 ^ n :=
      (Nat.le_div_iff_mul_le hpow).mpr hLower

    have hUpperDiv : t / 5 ^ n < u + 1 :=
      (Nat.div_lt_iff_lt_mul hpow).mpr hUpper

    omega

/--
The same equivalence written as membership in the `Finset.Ico` used by the
block-weight theorem.
-/
theorem fiveScale_eq_iff_mem_block
    {t n u : Nat} :
    FiveScale t n = u ↔
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n) := by
  rw [fiveScale_eq_iff_block]
  exact Finset.mem_Ico.symm

/--
Every canonical scale supplied by `exists_canonical_five_scale` therefore
places `t` in its corresponding complete factor-5 block.
-/
theorem canonical_scale_mem_block
    {t n : Nat}
    (hn : 24 ≤ FiveScale t n)
    (hu : FiveScale t n ≤ 119) :
    t ∈ Finset.Ico
      (FiveScale t n * 5 ^ n)
      ((FiveScale t n + 1) * 5 ^ n) := by
  have hEq :
      FiveScale t n = FiveScale t n := rfl
  exact fiveScale_eq_iff_mem_block.mp hEq

/--
For `t ≥ 120`, there is a canonical pair `(n,u)` with positive depth,
terminal scale in `24..119`, and `t` lying in the corresponding block.
-/
theorem exists_canonical_block
    {t : Nat}
    (ht : 120 ≤ t) :
    ∃ n u : Nat,
      1 ≤ n ∧
      24 ≤ u ∧
      u ≤ 119 ∧
      FiveScale t n = u ∧
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n) := by

  rcases exists_canonical_five_scale ht with
    ⟨n, hnPos, hLower, hUpper, hHigh⟩

  refine ⟨n, FiveScale t n, hnPos, hLower, hUpper, rfl, ?_⟩

  exact fiveScale_eq_iff_mem_block.mp rfl

end Erdos536813
