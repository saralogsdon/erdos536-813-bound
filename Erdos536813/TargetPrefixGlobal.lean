import Erdos536813.FiveCodeCharacterization

namespace Erdos536813

/-!
# Target prefixes occur inside the global factor-5 code list

The global regrouping is now exact:
`(m,k)` occurs in `GoodBaseFiveCodeList N` iff `m` is a positive
30-coprime core and `FiveBase m k ≤ N`.

To subtract a verified per-core deficit from that global sum, we must know
that every layer used by the target prefix is an actual code entry.
This file proves exactly that for both the finite and high-scale targets.
-/

/-- A positive 30-coprime core gives a positive base at every 5-adic depth. -/
theorem fiveBase_pos_of_goodThirtyCore
    {m k : Nat}
    (hm : GoodThirtyCore m) :
    0 < FiveBase m k := by
  unfold FiveBase
  exact Nat.mul_pos hm.1
    (Nat.pow_pos (by norm_num : 0 < (5 : Nat)))

/--
If the normalized scale at depth `k` is positive, then the corresponding
actual base `m * 5^k` is at most `N`.
-/
theorem fiveBase_le_of_fiveScale_pos
    {N m k : Nat}
    (hm : GoodThirtyCore m)
    (hPos : 1 ≤ FiveScale (N / m) k) :
    FiveBase m k ≤ N := by

  have hBasePos :
      0 < FiveBase m k :=
    fiveBase_pos_of_goodThirtyCore hm

  have hDiv :
      1 ≤ N / FiveBase m k := by
    rw [← fiveScale_div_base N m k]
    exact hPos

  have hMul :
      1 * FiveBase m k ≤ N :=
    (Nat.le_div_iff_mul_le hBasePos).mp hDiv

  simpa using hMul

/--
A positive normalized scale therefore produces an actual member of the
global five-code list.
-/
theorem fiveCode_mem_of_fiveScale_pos
    {N m k : Nat}
    (hm : GoodThirtyCore m)
    (hPos : 1 ≤ FiveScale (N / m) k) :
    (m, k) ∈ GoodBaseFiveCodeList N := by

  apply mem_goodBaseFiveCodeList_iff.mpr
  exact ⟨hm, fiveBase_le_of_fiveScale_pos hm hPos⟩

/--
If the final scale of a prefix is positive, every earlier layer of that
prefix occurs in the global code list.
-/
theorem fivePrefix_mem_global_of_final_scale_pos
    {N m r : Nat}
    (hm : GoodThirtyCore m)
    (hFinal : 1 ≤ FiveScale (N / m) r) :
    ∀ k ≤ r, (m, k) ∈ GoodBaseFiveCodeList N := by

  intro k hk

  have hMono :
      FiveScale (N / m) r ≤
        FiveScale (N / m) k :=
    fiveScale_antitone (N / m) hk

  have hPos :
      1 ≤ FiveScale (N / m) k := by
    omega

  exact fiveCode_mem_of_fiveScale_pos hm hPos

/--
A nonzero finite target can only occur once the outer normalized scale is
at least `15`.
-/
theorem finiteTargetDeficit_pos_implies_fifteen_le
    {t : Nat}
    (hPos : 0 < finiteTargetDeficit t) :
    15 ≤ t := by

  unfold finiteTargetDeficit at hPos
  split_ifs at hPos with hStrong hWeak
  · rcases hStrong with h45 | h80
    · omega
    · omega
  · rcases hWeak with h15 | h20 | h40 | h72
    · omega
    · omega
    · omega
    · omega
  · omega

/--
Consequently, whenever the finite target is nonzero, depth `1` is still an
actual positive scale.
-/
theorem finiteTargetDeficit_pos_implies_scale_one_pos
    {t : Nat}
    (hPos : 0 < finiteTargetDeficit t) :
    1 ≤ FiveScale t 1 := by

  have ht :
      15 ≤ t :=
    finiteTargetDeficit_pos_implies_fifteen_le hPos

  have hDiv :
      1 ≤ t / 5 := by
    apply (Nat.le_div_iff_mul_le
      (by norm_num : 0 < (5 : Nat))).mpr
    omega

  simpa [FiveScale] using hDiv

/--
Thus the two layers used by a nonzero finite target are genuine entries of
the global code list.
-/
theorem finiteTarget_prefix_mem_global
    {N m : Nat}
    (hm : GoodThirtyCore m)
    (hTarget :
      0 < finiteTargetDeficit (N / m)) :
    ∀ k ≤ 1, (m, k) ∈ GoodBaseFiveCodeList N := by

  have hFinal :
      1 ≤ FiveScale (N / m) 1 :=
    finiteTargetDeficit_pos_implies_scale_one_pos hTarget

  exact
    fivePrefix_mem_global_of_final_scale_pos
      hm hFinal

/--
For a high initial scale, the canonical safe target prefix consists entirely
of actual global code entries.
-/
theorem exists_canonical_safe_highTarget_prefix_mem_global
    {A : List Nat}
    {N m : Nat}
    (hm : GoodThirtyCore m)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (ht : 120 ≤ N / m) :
    ∃ n : Nat,
      1 ≤ n ∧
      24 ≤ FiveScale (N / m) n ∧
      FiveScale (N / m) n ≤ 119 ∧
      1 ≤
        FiveScale (N / m)
          (highSafeDepth n (FiveScale (N / m) n)) ∧
      (∀ k ≤ highSafeDepth n (FiveScale (N / m) n),
        (m, k) ∈ GoodBaseFiveCodeList N) ∧
      highFiberTarget n (FiveScale (N / m) n) +
          ActualFiveIntegerPrefix A N m
            (highSafeDepth n (FiveScale (N / m) n)) ≤
        FiveBaselinePrefix N m
          (highSafeDepth n (FiveScale (N / m) n)) := by

  rcases
    exists_canonical_safe_highTarget_bound
      (A := A) (N := N) (m := m)
      hm.1 hA ht
    with
      ⟨n, hn, hLower, hUpper, hFinal, hBound⟩

  have hMem :
      ∀ k ≤ highSafeDepth n (FiveScale (N / m) n),
        (m, k) ∈ GoodBaseFiveCodeList N :=
    fivePrefix_mem_global_of_final_scale_pos
      hm hFinal

  exact
    ⟨n, hn, hLower, hUpper, hFinal, hMem, hBound⟩

end Erdos536813
