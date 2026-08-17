import Erdos536813.GoodCoreQuotientDensityError

namespace Erdos536813

/--
Natural-number division differs from real division by less than one.
-/
theorem natDiv_cast_sub_realDiv_abs_lt_one
    {N t : Nat}
    (htPos : 0 < t) :
    |((N / t : Nat) : ℝ) -
        (N : ℝ) / (t : ℝ)| < 1 := by

  have htReal :
      0 < (t : ℝ) := by
    exact_mod_cast htPos

  have hMulLower :
      (N / t) * t ≤ N :=
    Nat.div_mul_le_self N t

  have hLower :
      ((N / t : Nat) : ℝ) ≤
        (N : ℝ) / (t : ℝ) := by
    apply
      (le_div_iff₀ htReal).mpr

    exact_mod_cast hMulLower

  have hMod :
      N % t < t :=
    Nat.mod_lt N htPos

  have hDecomp :
      N % t + t * (N / t) = N :=
    Nat.mod_add_div N t

  have hMulUpper :
      N < (N / t + 1) * t := by
    omega

  have hUpper :
      (N : ℝ) / (t : ℝ) <
        ((N / t : Nat) : ℝ) + 1 := by
    apply
      (div_lt_iff₀ htReal).mpr

    exact_mod_cast hMulUpper

  rw [abs_of_nonpos]
  · linarith
  · linarith

/--
Equivalently, the floor error has absolute value at most one.
-/
theorem natDiv_cast_sub_realDiv_abs_le_one
    {N t : Nat}
    (htPos : 0 < t) :
    |((N / t : Nat) : ℝ) -
        (N : ℝ) / (t : ℝ)| ≤ 1 := by

  exact le_of_lt
    (natDiv_cast_sub_realDiv_abs_lt_one htPos)

end Erdos536813
