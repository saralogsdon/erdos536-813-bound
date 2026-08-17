import Erdos536813.GoodCoreInitialBlocksNodup

namespace Erdos536813

/-- The number of positive good cores at most `X`. -/
noncomputable def GoodCoreCount
    (X : Nat) : Nat :=
  (GoodCoreFinset X).card

/-- The good-core counting function is monotone. -/
theorem goodCoreCount_mono
    {X Y : Nat}
    (hXY : X ≤ Y) :
    GoodCoreCount X ≤ GoodCoreCount Y := by

  unfold GoodCoreCount

  apply Finset.card_le_card

  intro m hm

  have hmData :=
    mem_goodCoreFinset_iff.mp hm

  apply mem_goodCoreFinset_iff.mpr

  exact
    ⟨Nat.le_trans hmData.1 hXY,
      hmData.2⟩

/--
For every cutoff `X`, the first `X/30` complete blocks contribute
`8*(X/30)` good cores.
-/
theorem eight_mul_div_thirty_le_goodCoreCount
    (X : Nat) :
    8 * (X / 30) ≤ GoodCoreCount X := by

  have hBlockBound :
      30 * (X / 30) ≤ X :=
    Nat.mul_div_le X 30

  have hCompleteBlocks :
      8 * (X / 30) ≤
        GoodCoreCount (30 * (X / 30)) := by
    simpa [GoodCoreCount] using
      eight_mul_le_goodCoreFinset_card
        (X / 30)

  exact Nat.le_trans
    hCompleteBlocks
    (goodCoreCount_mono hBlockBound)

/--
A convenient denominator-free density estimate: the good-core count differs
from density `4/15` by a uniformly bounded error.
-/
theorem four_mul_le_fifteen_mul_goodCoreCount_add
    (X : Nat) :
    4 * X ≤
      15 * GoodCoreCount X + 119 := by

  have hCount :
      8 * (X / 30) ≤ GoodCoreCount X :=
    eight_mul_div_thirty_le_goodCoreCount X

  have hMod :
      X % 30 < 30 :=
    Nat.mod_lt X
      (by norm_num : 0 < (30 : Nat))

  have hDecomp :
      X % 30 + 30 * (X / 30) = X :=
    Nat.mod_add_div X 30

  omega

end Erdos536813
