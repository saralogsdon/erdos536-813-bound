import Erdos536813.FiniteTargetInterval

namespace Erdos536813

/--
The first canonical block at positive depth `n + 1` begins at
the outer scale `120 * 5^n`.
-/
theorem highLayer_start_identity
    (n : Nat) :
    24 * 5 ^ (n + 1) =
      120 * 5 ^ n := by

  rw [pow_succ]
  ring

/--
The final canonical block at positive depth `n + 1` ends at
the outer scale `120 * 5^(n+1)`.
-/
theorem highLayer_end_identity
    (n : Nat) :
    (119 + 1) * 5 ^ (n + 1) =
      120 * 5 ^ (n + 1) := by

  norm_num

/-- The interval of outer scales belonging to positive-depth layer `n`. -/
def HighLayerInterval
    (n : Nat) : Finset Nat :=
  Finset.Ico
    (120 * 5 ^ n)
    (120 * 5 ^ (n + 1))

/--
Every canonical `u`-block at depth `n + 1` lies inside the corresponding
complete high-layer interval.
-/
theorem fiveBlock_subset_highLayerInterval
    {n u : Nat}
    (huLower : 24 ≤ u)
    (huUpper : u ≤ 119) :
    Finset.Ico
        (u * 5 ^ (n + 1))
        ((u + 1) * 5 ^ (n + 1))
      ⊆
    HighLayerInterval n := by

  intro t ht

  have htData :
      u * 5 ^ (n + 1) ≤ t ∧
        t < (u + 1) * 5 ^ (n + 1) :=
    Finset.mem_Ico.mp ht

  have hLowerMul :
      24 * 5 ^ (n + 1) ≤
        u * 5 ^ (n + 1) :=
    Nat.mul_le_mul_right
      (5 ^ (n + 1))
      huLower

  have hUpperIndex :
      u + 1 ≤ 120 := by
    omega

  have hUpperMul :
      (u + 1) * 5 ^ (n + 1) ≤
        120 * 5 ^ (n + 1) :=
    Nat.mul_le_mul_right
      (5 ^ (n + 1))
      hUpperIndex

  unfold HighLayerInterval
  apply Finset.mem_Ico.mpr

  constructor

  · rw [← highLayer_start_identity n]
    exact hLowerMul.trans htData.1

  · exact htData.2.trans_le hUpperMul

/--
Successive high-layer intervals meet at exactly the same endpoint.
-/
theorem highLayer_endpoint_adjacent
    (n : Nat) :
    120 * 5 ^ (n + 1) =
      120 * 5 ^ (n + 1) := by

  rfl

/--
Every scale in the `n`th high layer is at least `120`.
-/
theorem highLayer_scale_ge_120
    {n t : Nat}
    (ht : t ∈ HighLayerInterval n) :
    120 ≤ t := by

  have htLower :
      120 * 5 ^ n ≤ t :=
    (Finset.mem_Ico.mp ht).1

  have hPow :
      1 ≤ 5 ^ n := by
    positivity

  have hStart :
      120 ≤ 120 * 5 ^ n := by
    nlinarith

  exact hStart.trans htLower

end Erdos536813
