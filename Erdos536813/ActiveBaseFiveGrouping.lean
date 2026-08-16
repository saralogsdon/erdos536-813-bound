import Erdos536813.GoodBaseFiveDecomposition

namespace Erdos536813

/-!
# Reindexing the original active fiber sum by 5-adic chains

The upstream `5/6` proof sums `FiberIntegerList A q` over the active good
fiber bases `q`.  We first enlarge that sum to *all* good fiber bases
`q ≤ N`; the newly-added terms vanish because a non-active base has an empty
integer fiber.

We then reindex each good base by its canonical factor-5 code

    q ↦ (FiveCore q, FiveExponent q),

which is injective and reconstructs `q` exactly as

    q = FiveCore q * 5^(FiveExponent q).

This is the finite bookkeeping bridge needed before summing the verified
5-adic deficit chain over coprime-to-30 cores.
-/

/--
A computable Boolean test for the upstream predicate `GoodFiberBase`.

We deliberately do not write `decide (Erdos536.GoodFiberBase q)`: the
upstream predicate is an opaque definition, so typeclass synthesis does not
automatically unfold it to construct a `Decidable` instance.
-/
def goodFiberBaseBool (q : Nat) : Bool :=
  decide (0 < q) && decide (Nat.gcd q 6 = 1)

@[simp]
theorem goodFiberBaseBool_eq_true_iff
    (q : Nat) :
    goodFiberBaseBool q = true ↔
      Erdos536.GoodFiberBase q := by
  simp [goodFiberBaseBool, Erdos536.GoodFiberBase, Nat.Coprime]

/-- All good `2,3`-fiber bases up to `N`. -/
def GoodBaseUpToList (N : Nat) : List Nat :=
  (List.range (N + 1)).filter goodFiberBaseBool

theorem goodBaseUpToList_nodup
    (N : Nat) :
    (GoodBaseUpToList N).Nodup := by
  unfold GoodBaseUpToList
  exact List.nodup_range.filter goodFiberBaseBool

theorem mem_goodBaseUpToList
    {N q : Nat} :
    q ∈ GoodBaseUpToList N ↔
      q ≤ N ∧ Erdos536.GoodFiberBase q := by
  constructor
  · intro hq
    have hdata :
        q < N + 1 ∧ goodFiberBaseBool q = true := by
      simpa [GoodBaseUpToList] using hq
    exact
      ⟨Nat.le_of_lt_succ hdata.1,
       (goodFiberBaseBool_eq_true_iff q).mp hdata.2⟩
  · intro hq
    have hlt : q < N + 1 :=
      Nat.lt_succ_of_le hq.1
    have hgood :
        goodFiberBaseBool q = true :=
      (goodFiberBaseBool_eq_true_iff q).mpr hq.2
    simpa [GoodBaseUpToList, hlt, hgood]

/-- Every upstream active base is one of the good bases up to `N`. -/
theorem fiberActiveBaseList_subset_goodBaseUpToList
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    (Erdos536.FiberActiveBaseList A N).Subset
      (GoodBaseUpToList N) := by
  intro q hq
  apply mem_goodBaseUpToList.mpr
  exact
    ⟨Erdos536.fiberActiveBaseList_mem_range hq,
     Erdos536.fiberActiveBaseList_good_of_mem hA hq⟩

/--
If `q` never occurs as an encoded base of an element of `A`, then its
integer fiber is empty.
-/
theorem fiberIntegerList_eq_nil_of_not_mem_baseList
    {A : List Nat}
    {q : Nat}
    (hq : q ∉ Erdos536.FiberBaseList A) :
    Erdos536.FiberIntegerList A q = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro n hn
  exact hq (Erdos536.fiberIntegerList_mem_baseList_of_mem hn)

/--
On any ambient list of candidate bases, filtering by "actually occurs as a
base" or by our Boolean good-base test gives the same total integer-fiber
count.  The extra good bases have empty fibers.
-/
theorem fiberInteger_sum_filter_base_eq_good
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (L : List Nat) :
    ((L.filter
        (fun q => decide (q ∈ Erdos536.FiberBaseList A))).map
      (fun q => (Erdos536.FiberIntegerList A q).length)).sum
    =
    ((L.filter goodFiberBaseBool).map
      (fun q => (Erdos536.FiberIntegerList A q).length)).sum := by

  induction L with
  | nil =>
      simp
  | cons q L ih =>
      by_cases hBase : q ∈ Erdos536.FiberBaseList A
      · have hGood :
            Erdos536.GoodFiberBase q :=
          Erdos536.fiberBaseList_good_of_mem hA hBase
        have hGoodB :
            goodFiberBaseBool q = true :=
          (goodFiberBaseBool_eq_true_iff q).mpr hGood
        simp [hBase, hGoodB, ih]
      · have hNil :
            Erdos536.FiberIntegerList A q = [] :=
          fiberIntegerList_eq_nil_of_not_mem_baseList hBase
        by_cases hGood : Erdos536.GoodFiberBase q
        · have hGoodB :
              goodFiberBaseBool q = true :=
            (goodFiberBaseBool_eq_true_iff q).mpr hGood
          simp [hBase, hGoodB, hNil, ih]
        · have hGoodB :
              goodFiberBaseBool q = false := by
            cases hBool : goodFiberBaseBool q with
            | false =>
                exact hBool
            | true =>
                exfalso
                exact hGood
                  ((goodFiberBaseBool_eq_true_iff q).mp hBool)
          simp [hBase, hGoodB, ih]

/--
Thus the exact upstream active-fiber sum equals the sum over every good base
`q ≤ N`.
-/
theorem fiberActiveIntegerSum_eq_goodBaseIntegerSum
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    ((Erdos536.FiberActiveBaseList A N).map
      (fun q => (Erdos536.FiberIntegerList A q).length)).sum
    =
    ((GoodBaseUpToList N).map
      (fun q => (Erdos536.FiberIntegerList A q).length)).sum := by

  simpa [Erdos536.FiberActiveBaseList, GoodBaseUpToList] using
    (fiberInteger_sum_filter_base_eq_good
      (A := A) (N := N) hA (List.range (N + 1)))

/--
The global cardinality bound from the original proof can therefore be
restated using all good bases up to `N`.
-/
theorem card_le_goodBaseIntegerSum
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    A.length ≤
      ((GoodBaseUpToList N).map
        (fun q => (Erdos536.FiberIntegerList A q).length)).sum := by

  have hUpstream :=
    Erdos536.card_le_fiberActiveIntegerSlice_sum hA

  have hEq :=
    fiberActiveIntegerSum_eq_goodBaseIntegerSum hA

  rw [← hEq]
  exact hUpstream

/-- Canonical factor-5 code of a base. -/
def FiveCode (q : Nat) : Nat × Nat :=
  (FiveCore q, FiveExponent q)

/-- The factor-5 code reconstructs the original base exactly. -/
theorem fiveCode_reconstruct
    (q : Nat) :
    FiveBase (FiveCode q).1 (FiveCode q).2 = q := by
  simpa [FiveCode, FiveBase] using
    (fiveCore_mul_pow_fiveExponent q)

/-- The factor-5 code is injective. -/
theorem fiveCode_injective :
    Function.Injective FiveCode := by
  intro q r hCode
  have hCore :
      FiveCore q = FiveCore r := by
    simpa [FiveCode] using congrArg Prod.fst hCode
  have hExp :
      FiveExponent q = FiveExponent r := by
    simpa [FiveCode] using congrArg Prod.snd hCode

  calc
    q = FiveCore q * 5 ^ FiveExponent q :=
      (fiveCore_mul_pow_fiveExponent q).symm
    _ = FiveCore r * 5 ^ FiveExponent r := by
      rw [hCore, hExp]
    _ = r :=
      fiveCore_mul_pow_fiveExponent r

/-- Canonical factor-5 codes of all good bases up to `N`. -/
def GoodBaseFiveCodeList
    (N : Nat) : List (Nat × Nat) :=
  (GoodBaseUpToList N).map FiveCode

theorem goodBaseFiveCodeList_nodup
    (N : Nat) :
    (GoodBaseFiveCodeList N).Nodup := by
  unfold GoodBaseFiveCodeList
  exact (goodBaseUpToList_nodup N).map fiveCode_injective

/--
Every code in the good-base code list has a core coprime to `30`, and
reconstructs a good base at most `N`.
-/
theorem mem_goodBaseFiveCodeList_data
    {N m k : Nat}
    (h : (m, k) ∈ GoodBaseFiveCodeList N) :
    GoodThirtyCore m ∧
      FiveBase m k ≤ N ∧
      Erdos536.GoodFiberBase (FiveBase m k) := by

  rw [GoodBaseFiveCodeList, List.mem_map] at h
  rcases h with ⟨q, hq, hCode⟩

  have hqData :=
    mem_goodBaseUpToList.mp hq

  have hCoreData :=
    fiveCore_goodThirty_of_goodFiberBase hqData.2

  have hCore :
      FiveCore q = m := by
    simpa [FiveCode] using congrArg Prod.fst hCode

  have hExp :
      FiveExponent q = k := by
    simpa [FiveCode] using congrArg Prod.snd hCode

  have hRec :
      FiveBase m k = q := by
    unfold FiveBase
    rw [← hCore, ← hExp]
    exact fiveCore_mul_pow_fiveExponent q

  have hmThirty :
      GoodThirtyCore m := by
    rw [← hCore]
    exact hCoreData

  have hBound :
      FiveBase m k ≤ N := by
    rw [hRec]
    exact hqData.1

  have hGood :
      Erdos536.GoodFiberBase (FiveBase m k) := by
    rw [hRec]
    exact hqData.2

  exact ⟨hmThirty, hBound, hGood⟩

/--
The sum over all good bases is exactly the same sum reindexed by their
canonical `(30-coprime core, 5-adic depth)` codes.
-/
theorem goodBaseIntegerSum_eq_fiveCodeIntegerSum
    {A : List Nat}
    {N : Nat} :
    ((GoodBaseUpToList N).map
      (fun q => (Erdos536.FiberIntegerList A q).length)).sum
    =
    ((GoodBaseFiveCodeList N).map
      (fun c =>
        (Erdos536.FiberIntegerList A
          (FiveBase c.1 c.2)).length)).sum := by

  unfold GoodBaseFiveCodeList
  rw [List.map_map]

  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  simp [fiveCode_reconstruct]

/--
Hence the original set cardinality is bounded directly by the finite
factor-5-code sum.  This is the form to which the per-core deficit theorem
will be applied next.
-/
theorem card_le_fiveCodeIntegerSum
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    A.length ≤
      ((GoodBaseFiveCodeList N).map
        (fun c =>
          (Erdos536.FiberIntegerList A
            (FiveBase c.1 c.2)).length)).sum := by

  rw [← goodBaseIntegerSum_eq_fiveCodeIntegerSum]
  exact card_le_goodBaseIntegerSum hA

end Erdos536813
