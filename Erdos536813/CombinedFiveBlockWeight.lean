import Erdos536813.CanonicalFiveBlock

namespace Erdos536813

/--
The total combined-target weight on one canonical positive-depth block is
the previously computed factor-five block weight.
-/
theorem fiveBlock_combinedTargetWeight_sum
    {u n : Nat}
    (huLower : 24 ≤ u)
    (huUpper : u ≤ 119)
    (hn : 1 ≤ n) :
    (∑ t ∈
        Finset.Ico
          (u * 5 ^ n)
          ((u + 1) * 5 ^ n),
        combinedTargetWeight t)
      =
    (1 / (((5 ^ n : Nat) : ℚ))) *
      highTargetUWeight n u := by

  calc
    (∑ t ∈
        Finset.Ico
          (u * 5 ^ n)
          ((u + 1) * 5 ^ n),
        combinedTargetWeight t)
        =
      ∑ t ∈
        Finset.Ico
          (u * 5 ^ n)
          ((u + 1) * 5 ^ n),
        (highFiberTarget n u : ℚ) *
          outerWeight t := by
            apply Finset.sum_congr rfl
            intro t ht

            rw [
              combinedTargetWeight,
              combinedCoreTarget_eq_highFiberTarget_of_mem_fiveBlock
                huLower huUpper hn ht
            ]

    _ =
      (highFiberTarget n u : ℚ) *
        (∑ t ∈
          Finset.Ico
            (u * 5 ^ n)
            ((u + 1) * 5 ^ n),
          outerWeight t) := by
            rw [Finset.mul_sum]

    _ =
      (1 / (((5 ^ n : Nat) : ℚ))) *
        highTargetUWeight n u := by
            exact
              fiveBlock_highTarget_weight
                (lt_of_lt_of_le
                  (by norm_num : 0 < (24 : Nat))
                  huLower)

/--
At a fixed positive depth, summing over every terminal scale `24..119`
gives the exact base-plus-extra expression.
-/
theorem fixedDepth_combinedTargetWeight_sum
    (n : Nat)
    (hn : 1 ≤ n) :
    (∑ u ∈ Finset.Icc 24 119,
      ∑ t ∈
        Finset.Ico
          (u * 5 ^ n)
          ((u + 1) * 5 ^ n),
        combinedTargetWeight t)
      =
    (n : ℚ) *
        (1 / (((5 ^ n : Nat) : ℚ))) *
        (1 / 30) +
      (1 / (((5 ^ n : Nat) : ℚ))) *
        (1 / 75) := by

  calc
    (∑ u ∈ Finset.Icc 24 119,
      ∑ t ∈
        Finset.Ico
          (u * 5 ^ n)
          ((u + 1) * 5 ^ n),
        combinedTargetWeight t)
        =
      ∑ u ∈ Finset.Icc 24 119,
        (1 / (((5 ^ n : Nat) : ℚ))) *
          highTargetUWeight n u := by
            apply Finset.sum_congr rfl
            intro u hu

            have huData :
                24 ≤ u ∧ u ≤ 119 :=
              Finset.mem_Icc.mp hu

            exact
              fiveBlock_combinedTargetWeight_sum
                huData.1 huData.2 hn

    _ =
      (n : ℚ) *
          (1 / (((5 ^ n : Nat) : ℚ))) *
          (1 / 30) +
        (1 / (((5 ^ n : Nat) : ℚ))) *
          (1 / 75) :=
      fixedDepth_highTarget_weight_sum n

end Erdos536813
