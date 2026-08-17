import Erdos536813.HighLayerIntervals
import Erdos536813.FiveBlockCanonical

namespace Erdos536813

/--
The union of all 96 canonical terminal blocks at positive-depth layer `n`.
-/
def HighLayerBlockUnion
    (n : Nat) : Finset Nat :=
  (Finset.Icc 24 119).biUnion
    (fun u =>
      Finset.Ico
        (u * 5 ^ (n + 1))
        ((u + 1) * 5 ^ (n + 1)))

/--
The canonical blocks at one fixed positive depth cover exactly the
corresponding complete high-layer interval.
-/
theorem highLayerBlockUnion_eq
    (n : Nat) :
    HighLayerBlockUnion n =
      HighLayerInterval n := by

  ext t
  constructor

  · intro ht

    rcases Finset.mem_biUnion.mp ht with
      ⟨u, hu, htu⟩

    have huData :
        24 ≤ u ∧ u ≤ 119 :=
      Finset.mem_Icc.mp hu

    exact
      fiveBlock_subset_highLayerInterval
        huData.1 huData.2 htu

  · intro ht

    have htData :
        120 * 5 ^ n ≤ t ∧
          t < 120 * 5 ^ (n + 1) :=
      Finset.mem_Ico.mp ht

    let u : Nat :=
      FiveScale t (n + 1)

    have hPow :
        0 < 5 ^ (n + 1) :=
      Nat.pow_pos (by decide : 0 < (5 : Nat))

    have hLowerBlock :
        24 * 5 ^ (n + 1) ≤ t := by
      rw [highLayer_start_identity n]
      exact htData.1

    have huLower :
        24 ≤ u := by
      dsimp [u, FiveScale]
      exact
        (Nat.le_div_iff_mul_le hPow).mpr
          hLowerBlock

    have huLt :
        u < 120 := by
      dsimp [u, FiveScale]
      exact
        (Nat.div_lt_iff_lt_mul hPow).mpr
          htData.2

    have huUpper :
        u ≤ 119 := by
      omega

    have huMem :
        u ∈ Finset.Icc 24 119 :=
      Finset.mem_Icc.mpr
        ⟨huLower, huUpper⟩

    have hBlock :
        t ∈
          Finset.Ico
            (u * 5 ^ (n + 1))
            ((u + 1) * 5 ^ (n + 1)) := by

      apply fiveScale_eq_iff_mem_block.mp

      rfl

    exact
      Finset.mem_biUnion.mpr
        ⟨u, huMem, hBlock⟩

/--
Distinct canonical terminal blocks at the same depth are disjoint.
-/
theorem highLayer_blocks_disjoint
    {n u v : Nat}
    (huv : u ≠ v) :
    Disjoint
      (Finset.Ico
        (u * 5 ^ (n + 1))
        ((u + 1) * 5 ^ (n + 1)))
      (Finset.Ico
        (v * 5 ^ (n + 1))
        ((v + 1) * 5 ^ (n + 1))) := by

  rw [Finset.disjoint_left]
  intro t htu htv

  have huScale :
      FiveScale t (n + 1) = u :=
    fiveScale_eq_iff_mem_block.mpr htu

  have hvScale :
      FiveScale t (n + 1) = v :=
    fiveScale_eq_iff_mem_block.mpr htv

  apply huv

  calc
    u = FiveScale t (n + 1) := huScale.symm
    _ = v := hvScale

/--
The family of canonical blocks in one high layer is pairwise disjoint.
-/
theorem highLayer_blocks_pairwise_disjoint
    (n : Nat) :
    (↑(Finset.Icc 24 119) : Set Nat).Pairwise
      (fun u v =>
        Disjoint
          (Finset.Ico
            (u * 5 ^ (n + 1))
            ((u + 1) * 5 ^ (n + 1)))
          (Finset.Ico
            (v * 5 ^ (n + 1))
            ((v + 1) * 5 ^ (n + 1)))) := by

  intro u hu v hv huv

  exact highLayer_blocks_disjoint huv

/--
Consequently, summing the combined target weight over one complete high
layer is the same as summing over its 96 canonical blocks.
-/
theorem highLayer_combinedTargetWeight_sum
    (n : Nat) :
    (∑ t ∈ HighLayerInterval n,
      (combinedTargetWeight t : ℝ))
      =
    ∑ u ∈ Finset.Icc 24 119,
      ∑ t ∈
        Finset.Ico
          (u * 5 ^ (n + 1))
          ((u + 1) * 5 ^ (n + 1)),
        (combinedTargetWeight t : ℝ) := by

  rw [← highLayerBlockUnion_eq n]

  unfold HighLayerBlockUnion

  rw [
    Finset.sum_biUnion
      (highLayer_blocks_pairwise_disjoint n)
  ]

end Erdos536813
