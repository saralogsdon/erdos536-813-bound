import Erdos536813.FiveBlockPartition

namespace Erdos536813

/-!
# Canonicality and uniqueness of factor-5 blocks

`FiveBlockPartition` proves that

    FiveScale t n = u

is equivalent to membership of `t` in the interval block

    [u * 5^n, (u+1) * 5^n).

For the global weighted sum we also need to know that when

    1 ≤ n, 24 ≤ u ≤ 119,

this representation is the canonical first scale below `120`, and hence is
unique.  This prevents any double-counting when the high-scale sum is
reindexed by `(n,u)`.
-/

/-- Increasing the 5-adic depth can only decrease the scale. -/
theorem fiveScale_succ_le
    (t n : Nat) :
    FiveScale t (n + 1) ≤ FiveScale t n := by
  rw [fiveScale_succ]
  exact Nat.div_le_self _ _

/-- `FiveScale t` is antitone in the depth. -/
theorem fiveScale_antitone
    (t : Nat) :
    Antitone (FiveScale t) := by
  exact antitone_nat_of_succ_le (fiveScale_succ_le t)

/--
If `t` lies in a block of positive depth with terminal scale at least `24`,
then every earlier scale is at least `120`.
-/
theorem block_high_prefix
    {t n u : Nat}
    (hn : 1 ≤ n)
    (hu : 24 ≤ u)
    (hmem :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n)) :
    ∀ k < n, 120 ≤ FiveScale t k := by

  have hEq : FiveScale t n = u :=
    fiveScale_eq_iff_mem_block.mpr hmem

  have hnDecomp : n = (n - 1) + 1 := by
    omega

  have hStep :
      FiveScale t n =
        FiveScale t (n - 1) / 5 := by
    rw [hnDecomp]
    exact fiveScale_succ t (n - 1)

  have hQuot :
      FiveScale t (n - 1) / 5 = u := by
    calc
      FiveScale t (n - 1) / 5 = FiveScale t n := hStep.symm
      _ = u := hEq

  have huDiv :
      u ≤ FiveScale t (n - 1) / 5 := by
    rw [hQuot]

  have hPrevMul :
      u * 5 ≤ FiveScale t (n - 1) := by
    exact
      (Nat.le_div_iff_mul_le
        (by decide : 0 < (5 : Nat))).mp huDiv

  have hPrev :
      120 ≤ FiveScale t (n - 1) := by
    omega

  intro k hk

  have hkPrev : k ≤ n - 1 := by
    omega

  have hMono :
      FiveScale t (n - 1) ≤ FiveScale t k :=
    fiveScale_antitone t hkPrev

  omega

/--
Every valid positive-depth block in the terminal window is exactly a
canonical block: the terminal scale is below `120` and all earlier scales
are at least `120`.
-/
theorem block_is_canonical
    {t n u : Nat}
    (hn : 1 ≤ n)
    (huLower : 24 ≤ u)
    (huUpper : u ≤ 119)
    (hmem :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n)) :
    FiveScale t n = u ∧
      FiveScale t n < 120 ∧
      (∀ k < n, 120 ≤ FiveScale t k) := by

  have hEq : FiveScale t n = u :=
    fiveScale_eq_iff_mem_block.mpr hmem

  refine ⟨hEq, ?_, block_high_prefix hn huLower hmem⟩
  rw [hEq]
  omega

/--
Every valid positive-depth block in the terminal window consists only of
high outer scales `t ≥ 120`.
-/
theorem block_outer_scale_high
    {t n u : Nat}
    (hn : 1 ≤ n)
    (huLower : 24 ≤ u)
    (hmem :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n)) :
    120 ≤ t := by

  have hHigh :=
    block_high_prefix hn huLower hmem 0 (by omega)

  simpa [FiveScale] using hHigh

/--
Two valid canonical-window block representations of the same `t` are equal.
Thus the pair `(n,u)` is unique.
-/
theorem canonical_block_unique
    {t n u n' u' : Nat}
    (hn : 1 ≤ n)
    (hn' : 1 ≤ n')
    (huLower : 24 ≤ u)
    (huUpper : u ≤ 119)
    (huLower' : 24 ≤ u')
    (huUpper' : u' ≤ 119)
    (hmem :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n))
    (hmem' :
      t ∈ Finset.Ico
        (u' * 5 ^ n')
        ((u' + 1) * 5 ^ n')) :
    n = n' ∧ u = u' := by

  have hEq : FiveScale t n = u :=
    fiveScale_eq_iff_mem_block.mpr hmem

  have hEq' : FiveScale t n' = u' :=
    fiveScale_eq_iff_mem_block.mpr hmem'

  have hHigh :=
    block_high_prefix hn huLower hmem

  have hHigh' :=
    block_high_prefix hn' huLower' hmem'

  have hnn' : n = n' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt

    · have hEarlier :
          120 ≤ FiveScale t n :=
        hHigh' n hlt
      rw [hEq] at hEarlier
      omega

    · have hEarlier :
          120 ≤ FiveScale t n' :=
        hHigh n' hgt
      rw [hEq'] at hEarlier
      omega

  subst n'

  have huu' : u = u' := by
    calc
      u = FiveScale t n := hEq.symm
      _ = u' := hEq'

  exact ⟨rfl, huu'⟩

end Erdos536813
