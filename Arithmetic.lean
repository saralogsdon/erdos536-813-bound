import Mathlib

namespace Erdos536

/-- The exact rational arithmetic underlying the candidate coefficient. -/
theorem weighted_deficit_identity :
    (1 : ℚ) / 16 + 1 / 96 + 1 / 300 = 61 / 800 := by
  norm_num

/-- The final coefficient obtained from the 5/6 baseline and weighted deficit 61/800. -/
theorem coefficient_identity :
    (5 : ℚ) / 6 - (4 / 15) * (61 / 800) = 813 / 1000 := by
  norm_num

end Erdos536
