import Erdos536813.GlobalCoreReindex

namespace Erdos536813

/--
For a list without duplicates, summing a function over its associated
finset is the same as summing the mapped list.
-/
theorem finsetSum_eq_listMapSum_of_nodup
    {α : Type}
    [DecidableEq α]
    (L : List α)
    (f : α → Nat)
    (hL : L.Nodup) :
    (∑ x ∈ L.toFinset, f x) =
      (L.map f).sum := by
  induction L with
  | nil =>
      simp
  | cons a L ih =>
      have hData := List.nodup_cons.mp hL
      simp [hData.1, ih hData.2]

/--
The original five-code list sum used by the upstream cardinality theorem
equals our five-code finset sum.
-/
theorem fiveCodeIntegerListSum_eq_globalFiveCodeFinsetIntegerSum
    {A : List Nat}
    {N : Nat} :
    ((GoodBaseFiveCodeList N).map
      (fun c =>
        (Erdos536.FiberIntegerList A
          (FiveBase c.1 c.2)).length)).sum
      =
    GlobalFiveCodeFinsetIntegerSum A N := by
  classical

  have hSum :=
    finsetSum_eq_listMapSum_of_nodup
      (L := GoodBaseFiveCodeList N)
      (f := FiveCodeIntegerWeight A)
      (goodBaseFiveCodeList_nodup N)

  unfold GlobalFiveCodeFinsetIntegerSum

  simpa [FiveCodeIntegerWeight] using hSum.symm

/--
The original cardinality is bounded by the global integer-fiber sum
grouped into complete five-adic chains.
-/
theorem card_le_globalCoreIntegerSum
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    A.length ≤ GlobalCoreIntegerSum A N := by

  have hCard :=
    card_le_fiveCodeIntegerSum hA

  rw [
    fiveCodeIntegerListSum_eq_globalFiveCodeFinsetIntegerSum,
    globalFiveCodeFinsetIntegerSum_eq_globalCoreIntegerSum
  ] at hCard

  exact hCard

/--
Global cardinality plus the accumulated verified finite target saving
is bounded by the global complete-chain baseline.
-/
theorem card_add_globalFiniteTarget_le_globalCoreBaseline
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    A.length + GlobalFiniteTargetSum N
      ≤ GlobalCoreBaselineSum N := by

  have hCard :
      A.length ≤ GlobalCoreIntegerSum A N :=
    card_le_globalCoreIntegerSum hA

  have hSaving :
      GlobalFiniteTargetSum N +
          GlobalCoreIntegerSum A N
        ≤ GlobalCoreBaselineSum N :=
    globalFiniteTarget_add_globalCoreIntegerSum_le_baseline hA

  omega

end Erdos536813
