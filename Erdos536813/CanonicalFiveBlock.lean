import Erdos536813.FiveBlockScale

namespace Erdos536813

/--
Every depth preceding `n` remains in the high-scale regime for a canonical
factor-five block with terminal scale at least `24`.
-/
theorem fiveBlock_high_prefix
    {u n t k : Nat}
    (hu : 24 ≤ u)
    (ht :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n))
    (hk : k < n) :
    120 ≤ FiveScale t k := by

  have htLower :
      u * 5 ^ n ≤ t :=
    (Finset.mem_Ico.mp ht).1

  have hExponent :
      k + 1 ≤ n := by
    omega

  have hPow :
      5 ^ (k + 1) ≤ 5 ^ n :=
    Nat.pow_le_pow_right
      (by decide : 0 < (5 : Nat))
      hExponent

  have hProduct :
      120 * 5 ^ k ≤ u * 5 ^ n := by
    calc
      120 * 5 ^ k
          = 24 * 5 ^ (k + 1) := by
              simp [Nat.pow_succ]
              ring
      _ ≤ u * 5 ^ n :=
        Nat.mul_le_mul hu hPow

  have hToT :
      120 * 5 ^ k ≤ t :=
    Nat.le_trans hProduct htLower

  have hPowPos :
      0 < 5 ^ k :=
    Nat.pow_pos (by decide : 0 < (5 : Nat))

  unfold FiveScale
  exact
    (Nat.le_div_iff_mul_le hPowPos).mpr
      hToT

/--
For a block with terminal scale in `24..119` and positive depth, its stated
depth is precisely the canonical high depth.
-/
theorem canonicalHighDepth_eq_of_mem_fiveBlock
    {u n t : Nat}
    (huLower : 24 ≤ u)
    (huUpper : u ≤ 119)
    (hn : 1 ≤ n)
    (ht :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n)) :
    CanonicalHighDepth t = n := by

  have htHigh :
      120 ≤ t :=
    oneTwenty_le_of_mem_fiveBlock
      huLower hn ht

  have hScale :
      FiveScale t n = u :=
    fiveScale_eq_of_mem_fiveBlock ht

  have hCanonical :=
    canonicalHighDepth_spec htHigh

  have hCanonicalLe :
      CanonicalHighDepth t ≤ n := by
    by_contra hNot
    have hnBefore :
        n < CanonicalHighDepth t := by
      omega

    have hnHigh :
        120 ≤ FiveScale t n :=
      hCanonical.2.2.2 n hnBefore

    rw [hScale] at hnHigh
    omega

  have hDepthLe :
      n ≤ CanonicalHighDepth t := by
    by_contra hNot
    have hCanonicalBefore :
        CanonicalHighDepth t < n := by
      omega

    have hStillHigh :
        120 ≤
          FiveScale t (CanonicalHighDepth t) :=
      fiveBlock_high_prefix
        huLower ht hCanonicalBefore

    have hTerminalUpper :
        FiveScale t (CanonicalHighDepth t) ≤ 119 :=
      hCanonical.2.2.1

    omega

  exact Nat.le_antisymm hCanonicalLe hDepthLe

/--
On a canonical positive-depth block, the combined target is exactly the
high-fiber target attached to the block’s depth and terminal scale.
-/
theorem combinedCoreTarget_eq_highFiberTarget_of_mem_fiveBlock
    {u n t : Nat}
    (huLower : 24 ≤ u)
    (huUpper : u ≤ 119)
    (hn : 1 ≤ n)
    (ht :
      t ∈ Finset.Ico
        (u * 5 ^ n)
        ((u + 1) * 5 ^ n)) :
    CombinedCoreTarget t =
      highFiberTarget n u := by

  have htHigh :
      120 ≤ t :=
    oneTwenty_le_of_mem_fiveBlock
      huLower hn ht

  have hDepth :
      CanonicalHighDepth t = n :=
    canonicalHighDepth_eq_of_mem_fiveBlock
      huLower huUpper hn ht

  have hScale :
      FiveScale t n = u :=
    fiveScale_eq_of_mem_fiveBlock ht

  simp [
    CombinedCoreTarget,
    htHigh,
    hDepth,
    hScale
  ]

end Erdos536813
