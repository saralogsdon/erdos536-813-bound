import Mathlib

namespace Erdos536813

/-- Weighted deficit used in the candidate 0.813 argument. -/
theorem weighted_deficit_identity :
    (1 : ℚ) / 16 + 1 / 96 + 1 / 300 = 61 / 800 := by
  norm_num

/-- Exact arithmetic converting the 5/6 baseline to 813/1000. -/
theorem coefficient_identity :
    (5 : ℚ) / 6 - (4 / 15) * (61 / 800) = 813 / 1000 := by
  norm_num

end Erdos536813
