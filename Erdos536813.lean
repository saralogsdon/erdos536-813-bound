import Erdos536.FiveSixBound
import Arithmetic813

namespace Erdos536813

/-- Sanity check: our project sees the already-screened 5/6 theorem. -/
theorem imported_five_six_bound
    (N : Nat)
    (A : List Nat)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    A.length ≤ N - N / 6 := by
  exact Erdos536.five_six_bound_target N A hA

end Erdos536813
