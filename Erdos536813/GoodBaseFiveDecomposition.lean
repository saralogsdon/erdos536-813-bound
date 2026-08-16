import Erdos536813.ActualFiberBenchmark

namespace Erdos536813

/-!
# Canonical factor-5 decomposition of good fiber bases

The original `5/6` proof groups integers by a `GoodFiberBase q`, meaning

    0 < q  and  gcd(q, 6) = 1.

Our refined argument groups these bases further into factor-5 chains.  This
file makes that grouping canonical using Mathlib's `Nat.divMaxPow` and
`padicValNat`.

For every positive `q`, set

    FiveCore q     = q with its maximal power of 5 removed,
    FiveExponent q = v_5(q).

Then

    q = FiveCore q * 5^(FiveExponent q),

and `FiveCore q` is not divisible by 5.  If `q` is already coprime to 6,
the core is therefore coprime to 30.
-/

/-- Remove the maximal power of `5` from `q`. -/
def FiveCore (q : Nat) : Nat :=
  q.divMaxPow 5

/-- The exponent of the maximal power of `5` dividing `q`. -/
def FiveExponent (q : Nat) : Nat :=
  padicValNat 5 q

/-- The cores used to index our refined 5-adic chains. -/
def GoodThirtyCore (m : Nat) : Prop :=
  0 < m ∧ Nat.Coprime m 30

/-- Canonical reconstruction of any natural number from its factor-5 core. -/
theorem fiveCore_mul_pow_fiveExponent
    (q : Nat) :
    FiveCore q * 5 ^ FiveExponent q = q := by
  simpa [FiveCore, FiveExponent] using
    (Nat.divMaxPow_mul_pow_padicValNat 5 q)

/-- For positive `q`, its factor-5 core is not divisible by `5`. -/
theorem five_not_dvd_fiveCore
    {q : Nat}
    (hq : 0 < q) :
    ¬ 5 ∣ FiveCore q := by
  unfold FiveCore
  exact
    Nat.not_dvd_divMaxPow
      (p := 5)
      (n := q)
      (by norm_num)
      (Nat.ne_of_gt hq)

/-- The factor-5 core of a positive number is itself positive. -/
theorem fiveCore_pos
    {q : Nat}
    (hq : 0 < q) :
    0 < FiveCore q := by
  have hEq :=
    fiveCore_mul_pow_fiveExponent q
  have hPow :
      0 < 5 ^ FiveExponent q :=
    Nat.pow_pos (by norm_num)
  by_contra hNot
  have hZero : FiveCore q = 0 :=
    Nat.eq_zero_of_not_pos hNot
  rw [hZero, zero_mul] at hEq
  omega

/--
If `q` is a good base for the original 2,3-fiber decomposition, then after
removing its maximal power of `5` the remaining core is coprime to `30`.
-/
theorem fiveCore_goodThirty_of_goodFiberBase
    {q : Nat}
    (hq : Erdos536.GoodFiberBase q) :
    GoodThirtyCore (FiveCore q) := by

  have hcorePos :
      0 < FiveCore q :=
    fiveCore_pos hq.1

  have hcoreDvd :
      FiveCore q ∣ q := by
    refine ⟨5 ^ FiveExponent q, ?_⟩
    exact fiveCore_mul_pow_fiveExponent q

  have hcore6 :
      Nat.Coprime (FiveCore q) 6 :=
    hq.2.coprime_dvd_left hcoreDvd

  have hnot5 :
      ¬ 5 ∣ FiveCore q :=
    five_not_dvd_fiveCore hq.1

  have h5core :
      Nat.Coprime 5 (FiveCore q) :=
    Nat.prime_five.coprime_iff_not_dvd.mpr hnot5

  have hcore5 :
      Nat.Coprime (FiveCore q) 5 :=
    h5core.symm

  have hcore30 :
      Nat.Coprime (FiveCore q) (6 * 5) :=
    Nat.Coprime.mul_right hcore6 hcore5

  refine ⟨hcorePos, ?_⟩
  simpa using hcore30

/--
Every good base in the original proof belongs to a canonical factor-5 chain
whose core is coprime to `30`.
-/
theorem goodFiberBase_exists_five_decomposition
    {q : Nat}
    (hq : Erdos536.GoodFiberBase q) :
    ∃ m k : Nat,
      GoodThirtyCore m ∧
      q = m * 5 ^ k := by
  refine
    ⟨FiveCore q,
     FiveExponent q,
     fiveCore_goodThirty_of_goodFiberBase hq,
     ?_⟩
  exact (fiveCore_mul_pow_fiveExponent q).symm

/--
A decomposition `q = m * 5^k` with `m` coprime to `30` must be the canonical
one.  This gives uniqueness of both the core and the depth.
-/
theorem five_decomposition_unique
    {q m k : Nat}
    (hq : 0 < q)
    (hm : GoodThirtyCore m)
    (hEq : q = m * 5 ^ k) :
    m = FiveCore q ∧
      k = FiveExponent q := by

  have hm5 :
      Nat.Coprime m 5 :=
    hm.2.coprime_dvd_right
      (by norm_num : 5 ∣ 30)

  have h5m :
      Nat.Coprime 5 m :=
    hm5.symm

  have hnot5 :
      ¬ 5 ∣ m :=
    Nat.prime_five.coprime_iff_not_dvd.mp h5m

  have hPowEq :
      5 ^ k * m = q := by
    simpa [Nat.mul_comm] using hEq.symm

  have hPair :
      Nat.maxPowDvdDiv 5 q = (k, m) :=
    Nat.maxPowDvdDiv_of_pow_mul_eq
      (p := 5)
      (n := q)
      (k := k)
      (l := m)
      (Nat.ne_of_gt hq)
      hPowEq
      hnot5

  have hk :
      FiveExponent q = k := by
    unfold FiveExponent
    have hfst :=
      congrArg Prod.fst hPair
    simpa using hfst

  have hmcore :
      FiveCore q = m := by
    unfold FiveCore
    have hsnd :=
      congrArg Prod.snd hPair
    simpa using hsnd

  exact ⟨hmcore.symm, hk.symm⟩

/--
Equivalently, two good-thirty decompositions of the same positive base have
the same core and the same 5-adic depth.
-/
theorem goodThirty_five_decomposition_injective
    {q m k m' k' : Nat}
    (hq : 0 < q)
    (hm : GoodThirtyCore m)
    (hm' : GoodThirtyCore m')
    (hEq : q = m * 5 ^ k)
    (hEq' : q = m' * 5 ^ k') :
    m = m' ∧ k = k' := by

  have h1 :=
    five_decomposition_unique hq hm hEq

  have h2 :=
    five_decomposition_unique hq hm' hEq'

  exact
    ⟨h1.1.trans h2.1.symm,
     h1.2.trans h2.2.symm⟩

end Erdos536813
