import Erdos536813.GoodCoreCountUpper

namespace Erdos536813

/--
The good-core counting function differs from `(4/15)X` by a uniformly
bounded amount. We use the convenient symmetric error constant `120`.
-/
theorem goodCoreCount_density_error
    (X : Nat) :
    |15 * (GoodCoreCount X : ℝ) -
        4 * (X : ℝ)| ≤ 120 := by

  have hLowerNat :
      4 * X ≤
        15 * GoodCoreCount X + 119 :=
    four_mul_le_fifteen_mul_goodCoreCount_add X

  have hUpperNat :
      15 * GoodCoreCount X ≤
        4 * X + 120 :=
    fifteen_mul_goodCoreCount_le_four_mul_add X

  have hLowerReal :
      4 * (X : ℝ) ≤
        15 * (GoodCoreCount X : ℝ) + 119 := by
    exact_mod_cast hLowerNat

  have hUpperReal :
      15 * (GoodCoreCount X : ℝ) ≤
        4 * (X : ℝ) + 120 := by
    exact_mod_cast hUpperNat

  rw [abs_le]

  constructor <;> linarith

/--
Equivalently, after dividing by `15`, the discrepancy from density `4/15`
is at most `8`.
-/
theorem goodCoreCount_sub_density_bound
    (X : Nat) :
    |(GoodCoreCount X : ℝ) -
        (4 / 15 : ℝ) * X| ≤ 8 := by

  have h :=
    goodCoreCount_density_error X

  have hIdentity :
      (GoodCoreCount X : ℝ) -
          (4 / 15 : ℝ) * X
        =
      (1 / 15 : ℝ) *
        (15 * (GoodCoreCount X : ℝ) -
          4 * (X : ℝ)) := by
    ring

  rw [hIdentity, abs_mul]

  have hAbs :
      |(1 / 15 : ℝ)| = 1 / 15 := by
    norm_num

  rw [hAbs]

  nlinarith [abs_nonneg
    (15 * (GoodCoreCount X : ℝ) -
      4 * (X : ℝ))]

end Erdos536813
