import Erdos536813.FiveBlockCanonical

namespace Erdos536813

/-!
# Fixed-depth partition and weighted block sum

For a fixed 5-adic depth `n`, the terminal blocks with `24 ≤ u ≤ 119`
partition the annulus

    [24 * 5^n, 120 * 5^n).

On each such block, `FiveScale t n = u`, so the forced target
`highFiberTarget n u` is constant.  Combining this exact partition with
`fiveBlock_highTarget_weight` gives the complete weighted contribution at
depth `n`.
-/

/--
Membership in the fixed-depth annulus is equivalent to membership in one of
the terminal blocks `u = 24, ..., 119`.
-/
theorem mem_high_annulus_iff_exists_block
    {t n : Nat} :
    t ∈ Finset.Ico
        (24 * 5 ^ n)
        (120 * 5 ^ n) ↔
      ∃ u ∈ Finset.Icc 24 119,
        t ∈ Finset.Ico
          (u * 5 ^ n)
          ((u + 1) * 5 ^ n) := by

  have hpow : 0 < 5 ^ n :=
    Nat.pow_pos (by decide : 0 < (5 : Nat))

  constructor

  · intro ht
    rcases Finset.mem_Ico.mp ht with ⟨hLower, hUpper⟩

    let u : Nat := FiveScale t n

    have huLower : 24 ≤ u := by
      unfold u FiveScale
      exact
        (Nat.le_div_iff_mul_le hpow).mpr hLower

    have huLt : u < 120 := by
      unfold u FiveScale
      exact
        (Nat.div_lt_iff_lt_mul hpow).mpr hUpper

    have huUpper : u ≤ 119 := by
      omega

    have hmem :
        t ∈ Finset.Ico
          (u * 5 ^ n)
          ((u + 1) * 5 ^ n) := by
      exact fiveScale_eq_iff_mem_block.mp rfl

    exact
      ⟨u,
       Finset.mem_Icc.mpr ⟨huLower, huUpper⟩,
       hmem⟩

  · rintro ⟨u, hu, hmem⟩
    rcases Finset.mem_Icc.mp hu with ⟨huLower, huUpper⟩
    rcases Finset.mem_Ico.mp hmem with ⟨hBlockLower, hBlockUpper⟩

    have hLowerMul :
        24 * 5 ^ n ≤ u * 5 ^ n :=
      Nat.mul_le_mul_right (5 ^ n) huLower

    have hUpperMul :
        (u + 1) * 5 ^ n ≤ 120 * 5 ^ n := by
      apply Nat.mul_le_mul_right
      omega

    exact
      Finset.mem_Ico.mpr
        ⟨hLowerMul.trans hBlockLower,
         hBlockUpper.trans_le hUpperMul⟩

/--
At a fixed depth, a number cannot belong to two different terminal blocks.
-/
theorem fixedDepth_block_unique
    {t n u v : Nat}
    (htu :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n))
    (htv :
      t ∈ Finset.Ico
        (v * 5 ^ n)
        ((v + 1) * 5 ^ n)) :
    u = v := by

  have hu : FiveScale t n = u :=
    fiveScale_eq_iff_mem_block.mpr htu

  have hv : FiveScale t n = v :=
    fiveScale_eq_iff_mem_block.mpr htv

  exact hu.symm.trans hv

/--
The forced high target is constant on a fixed terminal block.
-/
theorem highFiberTarget_constant_on_block
    {t n u : Nat}
    (ht :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n)) :
    highFiberTarget n (FiveScale t n) =
      highFiberTarget n u := by

  have hEq : FiveScale t n = u :=
    fiveScale_eq_iff_mem_block.mpr ht

  rw [hEq]

/--
The exact weighted contribution of all terminal blocks at a fixed depth.
This is the block-sum form of `fixedDepth_highTarget_weight_sum`.
-/
theorem fixedDepth_highBlock_weight_sum
    (n : Nat) :
    (∑ u ∈ Finset.Icc 24 119,
      (highFiberTarget n u : ℚ) *
        (∑ t ∈
          Finset.Ico
            (u * 5 ^ n)
            ((u + 1) * 5 ^ n),
          outerWeight t)) =
      (n : ℚ) *
          (1 / (((5 ^ n : Nat) : ℚ))) *
          (1 / 30) +
        (1 / (((5 ^ n : Nat) : ℚ))) *
          (1 / 75) := by

  calc
    (∑ u ∈ Finset.Icc 24 119,
      (highFiberTarget n u : ℚ) *
        (∑ t ∈
          Finset.Ico
            (u * 5 ^ n)
            ((u + 1) * 5 ^ n),
          outerWeight t))
        =
      ∑ u ∈ Finset.Icc 24 119,
        (1 / (((5 ^ n : Nat) : ℚ))) *
          highTargetUWeight n u := by
            apply Finset.sum_congr rfl
            intro u hu
            have huLower : 24 ≤ u :=
              (Finset.mem_Icc.mp hu).1
            exact
              fiveBlock_highTarget_weight
                (by omega)

    _ =
      (n : ℚ) *
          (1 / (((5 ^ n : Nat) : ℚ))) *
          (1 / 30) +
        (1 / (((5 ^ n : Nat) : ℚ))) *
          (1 / 75) :=
      fixedDepth_highTarget_weight_sum n

end Erdos536813
