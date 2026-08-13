import Erdos536.FiveSixBound
import Mathlib

namespace Erdos536813

/-- Sanity check: our project sees the already-screened 5/6 theorem. -/
theorem imported_five_six_bound
    (N : Nat)
    (A : List Nat)
    (hA : Erdos536.LcmTriangleFreeUpTo N A) :
    A.length ≤ N - N / 6 := by
  exact Erdos536.five_six_bound_target N A hA

/-- Weighted deficit used in the candidate 0.813 argument. -/
theorem weighted_deficit_identity :
    (1 : ℚ) / 16 + 1 / 96 + 1 / 300 = 61 / 800 := by
  norm_num

/-- Exact arithmetic converting the 5/6 baseline to 813/1000. -/
theorem coefficient_identity :
    (5 : ℚ) / 6 - (4 / 15) * (61 / 800) = 813 / 1000 := by
  norm_num

/-
The first genuinely new 5-adic lemma.

If lcm(a,c)=w and 5 is coprime to w, then moving a up one 5-adic
layer multiplies the common lcm by 5.
-/
theorem lcm_five_mul_of_lcm_eq
    {a c w : Nat}
    (hac : Nat.lcm a c = w)
    (h5w : Nat.Coprime 5 w) :
    Nat.lcm (5 * a) c = 5 * w := by
  rw [Nat.lcm_eq_iff]
  have haW : a ∣ w := by
    rw [← hac]
    exact Nat.dvd_lcm_left a c
  have hcW : c ∣ w := by
    rw [← hac]
    exact Nat.dvd_lcm_right a c
  constructor
  · exact Nat.mul_dvd_mul_left 5 haW
  constructor
  · exact Nat.dvd_trans hcW (Nat.dvd_mul_left w 5)
  · intro d h5a hc
    have h5 : 5 ∣ d := by
      exact Nat.dvd_trans (Nat.dvd_mul_right 5 a) h5a
    have ha : a ∣ d := by
      exact Nat.dvd_trans (Nat.dvd_mul_left a 5) h5a
    have hw : w ∣ d := by
      rw [← hac]
      exact Nat.lcm_dvd ha hc
    exact h5w.mul_dvd_of_dvd_of_dvd h5 hw

/--
If `a,b,c` have common pairwise LCM `w`, and `5` is coprime to `w`,
then moving `a,b` up one 5-adic layer preserves equality of the three
pairwise LCMs, with new common value `5*w`.
-/
theorem lift_two_by_five_pairwise_lcms
    {a b c w : Nat}
    (hab : Nat.lcm a b = w)
    (hac : Nat.lcm a c = w)
    (hbc : Nat.lcm b c = w)
    (h5w : Nat.Coprime 5 w) :
    Nat.lcm (5 * a) (5 * b) = 5 * w ∧
      Nat.lcm (5 * a) c = 5 * w ∧
        Nat.lcm (5 * b) c = 5 * w := by
  constructor
  · calc
      Nat.lcm (5 * a) (5 * b) = 5 * Nat.lcm a b := by
        rw [Nat.lcm_mul_left]
      _ = 5 * w := by rw [hab]
  constructor
  · exact lcm_five_mul_of_lcm_eq hac h5w
  · exact lcm_five_mul_of_lcm_eq hbc h5w

/--
Same result stated in the exact equality form used by the Erdős #536
forbidden configuration.
-/
theorem lift_two_by_five_equal_pairwise_lcms
    {a b c w : Nat}
    (hab : Nat.lcm a b = w)
    (hac : Nat.lcm a c = w)
    (hbc : Nat.lcm b c = w)
    (h5w : Nat.Coprime 5 w) :
    Nat.lcm (5 * a) (5 * b) = Nat.lcm (5 * a) c ∧
      Nat.lcm (5 * a) c = Nat.lcm (5 * b) c := by
  rcases lift_two_by_five_pairwise_lcms hab hac hbc h5w with ⟨hAB, hAC, hBC⟩
  exact ⟨hAB.trans hAC.symm, hAC.trans hBC.symm⟩

/--
If `a,b,c` form an LCM triangle in a 5-free layer, then lifting `a,b`
to the next 5-adic layer produces another LCM triangle, provided the
lower point `c` is not divisible by 5.
-/
theorem lift_two_by_five_is_lcmTriangle
    {a b c w : Nat}
    (hab_ne : a ≠ b)
    (hab : Nat.lcm a b = w)
    (hac : Nat.lcm a c = w)
    (hbc : Nat.lcm b c = w)
    (h5w : Nat.Coprime 5 w)
    (h5c : ¬ 5 ∣ c) :
    Erdos536.IsLcmTriangle (5 * a) (5 * b) c := by
  rcases lift_two_by_five_pairwise_lcms hab hac hbc h5w with ⟨hAB, hAC, hBC⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hab_ne
    omega
  · intro h
    apply h5c
    rw [← h]
    exact Nat.dvd_mul_right 5 a
  · intro h
    apply h5c
    rw [← h]
    exact Nat.dvd_mul_right 5 b
  · exact hAB.trans hAC.symm
  · exact hAC.trans hBC.symm

/--
Convenient form: start from an existing `IsLcmTriangle` and lift the
first two vertices by 5.
-/
theorem lift_two_by_five_is_lcmTriangle_of_triangle
    {a b c : Nat}
    (htri : Erdos536.IsLcmTriangle a b c)
    (h5w : Nat.Coprime 5 (Nat.lcm a b))
    (h5c : ¬ 5 ∣ c) :
    Erdos536.IsLcmTriangle (5 * a) (5 * b) c := by
  rcases htri with ⟨hab_ne, _hac_ne, _hbc_ne, habac, hacbc⟩
  apply lift_two_by_five_is_lcmTriangle
      (w := Nat.lcm a b) hab_ne rfl
  · exact habac.symm
  · exact (habac.trans hacbc).symm
  · exact h5w
  · exact h5c


/--
`S` is inclusion-maximal Gamma-free inside the ambient board `D`.

This is deliberately an inclusion-maximal notion.  Later we will show that
a maximum-cardinality Gamma-free slice is automatically maximal in this sense.
-/
def MaximalGammaFreeIn
    (D S : List Erdos536.GridPoint) : Prop :=
  Erdos536.GammaFree S ∧
    ∀ c ∈ D, c ∉ S → ¬ Erdos536.GammaFree (c :: S)

/--
If `S` is maximal Gamma-free in `D` and `c ∈ D \ S`, then adjoining `c`
creates a Gamma-pattern, and that Gamma-pattern must involve the new point `c`.
-/
theorem maximalGammaFree_add_creates_gamma
    {D S : List Erdos536.GridPoint}
    {c : Erdos536.GridPoint}
    (hMax : MaximalGammaFreeIn D S)
    (hcD : c ∈ D)
    (hcS : c ∉ S) :
    ∃ top left down : Erdos536.GridPoint,
      top ∈ c :: S ∧
      left ∈ c :: S ∧
      down ∈ c :: S ∧
      Erdos536.GammaPattern top left down ∧
      (top = c ∨ left = c ∨ down = c) := by
  rcases hMax with ⟨hGF, hMaximal⟩
  have hGF' :
      S.Nodup ∧
        ∀ top ∈ S, ∀ left ∈ S, ∀ down ∈ S,
          ¬ Erdos536.GammaPattern top left down := by
    simpa [Erdos536.GammaFree] using hGF
  rcases hGF' with ⟨hSNodup, hNoGammaS⟩
  have hNotGF : ¬ Erdos536.GammaFree (c :: S) :=
    hMaximal c hcD hcS
  have hConsNodup : (c :: S).Nodup := by
    exact List.nodup_cons.mpr ⟨hcS, hSNodup⟩
  have hExists :
      ∃ top ∈ c :: S, ∃ left ∈ c :: S, ∃ down ∈ c :: S,
        Erdos536.GammaPattern top left down := by
    by_contra hNoExists
    apply hNotGF
    constructor
    · exact hConsNodup
    · intro top htop left hleft down hdown hGamma
      apply hNoExists
      exact ⟨top, htop, left, hleft, down, hdown, hGamma⟩
  rcases hExists with
    ⟨top, htop, left, hleft, down, hdown, hGamma⟩
  refine ⟨top, left, down, htop, hleft, hdown, hGamma, ?_⟩
  rcases List.mem_cons.mp htop with htopc | htopS
  · exact Or.inl htopc
  rcases List.mem_cons.mp hleft with hleftc | hleftS
  · exact Or.inr (Or.inl hleftc)
  rcases List.mem_cons.mp hdown with hdownc | hdownS
  · exact Or.inr (Or.inr hdownc)
  · exact False.elim ((hNoGammaS top htopS left hleftS down hdownS) hGamma)


/--
A missing point in a maximal Gamma-free family creates a Gamma-pattern with
two genuinely old vertices from `S`.  We record the three possible roles of
the new point `c`.
-/
theorem maximalGammaFree_missing_point_has_old_pair
    {D S : List Erdos536.GridPoint}
    {c : Erdos536.GridPoint}
    (hMax : MaximalGammaFreeIn D S)
    (hcD : c ∈ D)
    (hcS : c ∉ S) :
    ∃ u v : Erdos536.GridPoint,
      u ∈ S ∧
      v ∈ S ∧
      (Erdos536.GammaPattern c u v ∨
        Erdos536.GammaPattern u c v ∨
        Erdos536.GammaPattern u v c) := by
  rcases maximalGammaFree_add_creates_gamma hMax hcD hcS with
    ⟨top, left, down, htop, hleft, hdown, hGamma, hcRole⟩
  have hDistinct := Erdos536.gamma_points_pairwise_distinct hGamma
  rcases hDistinct with ⟨hTopLeft, hTopDown, hLeftDown⟩
  rcases hcRole with htopc | hleftc | hdownc
  · have hleftS : left ∈ S := by
      rcases List.mem_cons.mp hleft with hleftc' | hleftS
      · exfalso
        exact hTopLeft (htopc.trans hleftc'.symm)
      · exact hleftS
    have hdownS : down ∈ S := by
      rcases List.mem_cons.mp hdown with hdownc' | hdownS
      · exfalso
        exact hTopDown (htopc.trans hdownc'.symm)
      · exact hdownS
    refine ⟨left, down, hleftS, hdownS, Or.inl ?_⟩
    simpa [htopc] using hGamma
  · have htopS : top ∈ S := by
      rcases List.mem_cons.mp htop with htopc' | htopS
      · exfalso
        exact hTopLeft (htopc'.trans hleftc.symm)
      · exact htopS
    have hdownS : down ∈ S := by
      rcases List.mem_cons.mp hdown with hdownc' | hdownS
      · exfalso
        exact hLeftDown (hleftc.trans hdownc'.symm)
      · exact hdownS
    refine ⟨top, down, htopS, hdownS, Or.inr (Or.inl ?_)⟩
    simpa [hleftc] using hGamma
  · have htopS : top ∈ S := by
      rcases List.mem_cons.mp htop with htopc' | htopS
      · exfalso
        exact hTopDown (htopc'.trans hdownc.symm)
      · exact htopS
    have hleftS : left ∈ S := by
      rcases List.mem_cons.mp hleft with hleftc' | hleftS
      · exfalso
        exact hLeftDown (hleftc'.trans hdownc.symm)
      · exact hleftS
    refine ⟨top, left, htopS, hleftS, Or.inr (Or.inr ?_)⟩
    simpa [hdownc] using hGamma

end Erdos536813
