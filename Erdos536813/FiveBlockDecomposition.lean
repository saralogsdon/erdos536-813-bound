import Erdos536813.FiberTarget

namespace Erdos536813

/-!
# Canonical factor-5 block decomposition

For every `t ≥ 120`, choose the first index `n` at which the scale

    FiveScale t n = t / 5^n

drops below `120`.

Minimality gives `FiveScale t k ≥ 120` for every `k < n`. Since `n > 0`,
the preceding scale is at least `120`, so division by `5` shows that the
terminal scale lies in the canonical window `24..119`.

This is exactly the scale decomposition needed to feed an arbitrary high
`t` into `highFiberTarget_le_fiberPrefix`.
-/

/--
For every `t ≥ 120`, there is a canonical first scale below `120`.
Its value lies in `24..119`, and all preceding scales lie in the high
`T ≥ 120` regime.
-/
theorem exists_canonical_five_scale
    {t : Nat}
    (ht : 120 ≤ t) :
    ∃ n : Nat,
      1 ≤ n ∧
      24 ≤ FiveScale t n ∧
      FiveScale t n ≤ 119 ∧
      (∀ k < n, 120 ≤ FiveScale t k) := by

  have hexists : ∃ n : Nat, FiveScale t n < 120 := by
    refine ⟨t, ?_⟩
    unfold FiveScale
    have hpow : t < 5 ^ t := by
      exact Nat.lt_pow_self (by decide : 1 < (5 : Nat))
    have hdiv : t / 5 ^ t = 0 :=
      Nat.div_eq_of_lt hpow
    rw [hdiv]
    norm_num

  let n : Nat := Nat.find hexists

  have hTerminal : FiveScale t n < 120 := by
    exact Nat.find_spec hexists

    have hHigh :
      ∀ k < n, 120 ≤ FiveScale t k := by
    intro k hk
    have hNot :
        ¬ FiveScale t k < 120 :=
      Nat.find_min hexists hk
    omega

  have hnZero : n ≠ 0 := by
    intro hn
    have hScaleZero : FiveScale t n = t := by
      simp [hn, FiveScale]
    rw [hScaleZero] at hTerminal
    omega

  have hnPos : 1 ≤ n :=
    Nat.one_le_iff_ne_zero.mpr hnZero

  have hLower : 24 ≤ FiveScale t n := by
    have hPrev :
        120 ≤ FiveScale t (n - 1) := by
      exact hHigh (n - 1) (by omega)

    have hStep :
        FiveScale t n =
          FiveScale t (n - 1) / 5 := by
      have hnDecomp : n = (n - 1) + 1 := by
        omega
      rw [hnDecomp]
      exact fiveScale_succ t (n - 1)

    rw [hStep]
    omega

  have hUpper : FiveScale t n ≤ 119 := by
    omega

  exact ⟨n, hnPos, hLower, hUpper, hHigh⟩

/--
Consequently, every actual 5-adic fiber with `t ≥ 120` admits a canonical
index at which the already-proved high-scale target theorem applies.
-/
theorem exists_canonical_highFiberTarget_bound
    {t m N : Nat}
    {A : List Nat}
    {F : Nat → List Erdos536.GridPoint}
    (ht : 120 ≤ t)
    (hm : 0 < m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hSelected :
      ∀ r : Nat,
        Erdos536.FiberSelectedComplete
          (F r) A (FiveBase m r))
    (hSub :
      ∀ r : Nat,
        (F r).Subset
          (Erdos536.FiberRegionList 1 (FiveScale t r))) :
    ∃ n : Nat,
      1 ≤ n ∧
      24 ≤ FiveScale t n ∧
      FiveScale t n ≤ 119 ∧
      highFiberTarget n (FiveScale t n) ≤
        PrefixDeficit (FiberSliceDeficit t F) (n + 2) := by

  rcases exists_canonical_five_scale ht with
    ⟨n, hnPos, hLower, hUpper, hHigh⟩

  have hTarget :
      highFiberTarget n (FiveScale t n) ≤
        PrefixDeficit (FiberSliceDeficit t F) (n + 2) :=
    highFiberTarget_le_fiberPrefix
      hm hA hSelected hSub hHigh

  exact ⟨n, hnPos, hLower, hUpper, hTarget⟩

end Erdos536813
