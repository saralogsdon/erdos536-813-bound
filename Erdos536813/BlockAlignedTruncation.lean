import Erdos536813.HighLayerUnionInterval

namespace Erdos536813

/--
The finite interval `1..119` is the half-open interval `[1,120)`.
-/
theorem finiteTargetInterval_eq :
    Finset.Icc 1 119 =
      Finset.Ico 1 120 := by

  ext t
  simp
  omega

/--
For every `d`, the truncation endpoint `120 * 5^d - 1` describes the
half-open interval ending at `120 * 5^d`.
-/
theorem blockTruncationInterval_eq
    (d : Nat) :
    Finset.Icc 1 (120 * 5 ^ d - 1) =
      Finset.Ico 1 (120 * 5 ^ d) := by

  have hPow :
      1 ≤ 5 ^ d := by
    positivity

  have hEndpoint :
      1 ≤ 120 * 5 ^ d := by
    nlinarith

  ext t
  simp
  omega

/--
The interval from `1` to the block endpoint splits into the finite part
and the complete high-layer part.
-/
theorem blockTruncationInterval_split
    (d : Nat) :
    Finset.Ico 1 (120 * 5 ^ d) =
      Finset.Ico 1 120 ∪
        Finset.Ico 120 (120 * 5 ^ d) := by

  have hPow :
      1 ≤ 5 ^ d := by
    positivity

  have hEndpoint :
      120 ≤ 120 * 5 ^ d := by
    nlinarith

  ext t
  simp
  omega

/--
The finite interval and the high-layer interval are disjoint.
-/
theorem finiteTargetInterval_disjoint_highInterval
    (d : Nat) :
    Disjoint
      (Finset.Ico 1 120)
      (Finset.Ico 120 (120 * 5 ^ d)) := by

  rw [Finset.disjoint_left]
  intro t htFinite htHigh

  have htFiniteData :
      1 ≤ t ∧ t < 120 :=
    Finset.mem_Ico.mp htFinite

  have htHighData :
      120 ≤ t ∧ t < 120 * 5 ^ d :=
    Finset.mem_Ico.mp htHigh

  omega

/--
Every block-aligned weighted target is exactly an ordinary truncated
weighted target, with truncation endpoint `120 * 5^d - 1`.
-/
theorem truncatedWeightedTarget_blockEndpoint_eq
    (d : Nat) :
    TruncatedWeightedTarget
        (120 * 5 ^ d - 1)
      =
    BlockAlignedWeightedTarget d := by

  rw [
    truncatedWeightedTarget_eq_combinedTargetWeight_sum,
    blockTruncationInterval_eq,
    blockTruncationInterval_split,
    Finset.sum_union
      (finiteTargetInterval_disjoint_highInterval d)
  ]

  have hFinite :
      (∑ t ∈ Finset.Ico 1 120,
        (combinedTargetWeight t : ℝ))
        =
      TruncatedWeightedTarget 119 := by

    rw [← finiteTargetInterval_eq]

    exact
      (truncatedWeightedTarget_eq_combinedTargetWeight_sum
        119).symm

  have hHigh :
      (∑ t ∈ Finset.Ico 120 (120 * 5 ^ d),
        (combinedTargetWeight t : ℝ))
        =
      ExpandedHighBlockWeight d := by

    exact
      (expandedHighBlockWeight_eq_interval_sum d).symm

  rw [hFinite, hHigh]

  exact
    truncatedWeightedTarget_119_add_expandedHighBlockWeight_eq d

end Erdos536813
