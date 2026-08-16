import Erdos536813.GlobalBaselineReindex

namespace Erdos536813

/--
Applying the canonical five-code to `q` and then scaling the corresponding
baseline recovers the original quotient `N / q`.
-/
theorem fiveScale_fiveCode_eq_div
    (N q : Nat) :
    FiveScale
        (N / (FiveCode q).1)
        (FiveCode q).2
      =
    N / q := by
  unfold FiveScale
  rw [Nat.div_div_eq_div_mul]

  simpa [FiveBase] using
    congrArg (fun d : Nat => N / d)
      (fiveCode_reconstruct q)

/--
The baseline sum indexed by ordinary good bases is equal to the same sum
indexed by their canonical five-codes.
-/
theorem goodBaseBaselineSum_eq_fiveCodeBaselineSum
    {N : Nat} :
    ((GoodBaseUpToList N).map
      (fun q => L23 (N / q))).sum
      =
    ((GoodBaseFiveCodeList N).map
      (fun p =>
        L23 (FiveScale (N / p.1) p.2))).sum := by

  unfold GoodBaseFiveCodeList
  rw [List.map_map]

  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq

  simp [fiveScale_fiveCode_eq_div]

/--
Consequently, the global core baseline is exactly the sum of `L23 (N / q)`
over all good bases `q ≤ N`.
-/
theorem goodBaseBaselineSum_eq_globalCoreBaselineSum
    {N : Nat} :
    ((GoodBaseUpToList N).map
      (fun q => L23 (N / q))).sum
      =
    GlobalCoreBaselineSum N := by

  rw [
    goodBaseBaselineSum_eq_fiveCodeBaselineSum,
    fiveCodeBaselineListSum_eq_globalCoreBaselineSum
  ]

end Erdos536813
