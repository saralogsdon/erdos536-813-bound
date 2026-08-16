import Erdos536813.GlobalCardinalitySaving
import Erdos536813.FiveBlockDecomposition

namespace Erdos536813

/--
For a high scale `t`, choose its canonical first depth at which the
normalized scale lies in `24..119`. For `t < 120`, use depth zero.
-/
noncomputable def CanonicalHighDepth
    (t : Nat) : Nat :=
  if ht : 120 ≤ t then
    Classical.choose (exists_canonical_five_scale ht)
  else
    0

/--
The canonical high depth satisfies all the properties provided by
`exists_canonical_five_scale`.
-/
theorem canonicalHighDepth_spec
    {t : Nat}
    (ht : 120 ≤ t) :
    1 ≤ CanonicalHighDepth t ∧
      24 ≤ FiveScale t (CanonicalHighDepth t) ∧
      FiveScale t (CanonicalHighDepth t) ≤ 119 ∧
      ∀ k < CanonicalHighDepth t,
        120 ≤ FiveScale t k := by
  unfold CanonicalHighDepth
  rw [dif_pos ht]

  exact
    Classical.choose_spec
      (exists_canonical_five_scale ht)

/-- The canonical high depth is positive. -/
theorem canonicalHighDepth_pos
    {t : Nat}
    (ht : 120 ≤ t) :
    1 ≤ CanonicalHighDepth t :=
  (canonicalHighDepth_spec ht).1

/-- Its terminal scale lies in the canonical window. -/
theorem canonicalHighDepth_terminal_window
    {t : Nat}
    (ht : 120 ≤ t) :
    24 ≤ FiveScale t (CanonicalHighDepth t) ∧
      FiveScale t (CanonicalHighDepth t) ≤ 119 :=
  ⟨(canonicalHighDepth_spec ht).2.1,
   (canonicalHighDepth_spec ht).2.2.1⟩

/-- Every earlier depth remains in the high-scale regime. -/
theorem canonicalHighDepth_high_prefix
    {t : Nat}
    (ht : 120 ≤ t) :
    ∀ k < CanonicalHighDepth t,
      120 ≤ FiveScale t k :=
  (canonicalHighDepth_spec ht).2.2.2

end Erdos536813
