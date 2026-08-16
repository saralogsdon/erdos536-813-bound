import Erdos536813.GlobalBaselineValueNodup

namespace Erdos536813

/--
The global core baseline is at most the number of positive integers up to
`N` that are not divisible by six.
-/
theorem globalCoreBaselineSum_le_nonSixUpToList_length
    {N : Nat} :
    GlobalCoreBaselineSum N
      ≤
    (Erdos536.NonSixUpToList N).length := by

  have hLength :
      (GlobalBaselineValueList N).length
        ≤
      (Erdos536.NonSixUpToList N).length :=
    nodup_length_le_of_subset
      globalBaselineValueList_nodup
      globalBaselineValueList_subset_nonSixUpToList

  rw [
    globalBaselineValueList_length_eq_globalCoreBaselineSum
  ] at hLength

  exact hLength

/--
Therefore the global core baseline satisfies the original five-six counting
bound.
-/
theorem globalCoreBaselineSum_le_fiveSixBound
    (N : Nat) :
    GlobalCoreBaselineSum N
      ≤
    N - N / 6 := by

  exact Nat.le_trans
    globalCoreBaselineSum_le_nonSixUpToList_length
    (Erdos536.nonSixUpToList_length_le N)

/--
The cardinality of an admissible family, plus the entire finite/high saving,
is bounded by the original five-six benchmark.
-/
theorem card_add_globalCombinedTarget_le_fiveSixBound
    {A : List Nat}
    {N : Nat}
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    A.length + GlobalCombinedTargetSum N
      ≤
    N - N / 6 := by

  exact Nat.le_trans
    (card_add_globalCombinedTarget_le_globalCoreBaseline hA)
    (globalCoreBaselineSum_le_fiveSixBound N)

end Erdos536813
