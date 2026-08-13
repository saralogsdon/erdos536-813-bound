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


/--
If 5 is coprime to the fiber base, then it is coprime to every value in
that 2,3-fiber.
-/
theorem coprime_five_fiberValue
    {m : Nat}
    (h5m : Nat.Coprime 5 m)
    (p : Erdos536.GridPoint) :
    Nat.Coprime 5 (Erdos536.fiberValue m p) := by
  exact Nat.Coprime.mul_right
    (Nat.Coprime.mul_right
      h5m
      (Nat.Coprime.pow_right p.i (by decide : Nat.Coprime 5 2)))
    (Nat.Coprime.pow_right p.j (by decide : Nat.Coprime 5 3))

/-- In a 5-free fiber, no fiber value is divisible by 5. -/
theorem not_five_dvd_fiberValue
    {m : Nat}
    (h5m : Nat.Coprime 5 m)
    (p : Erdos536.GridPoint) :
    ¬ 5 ∣ Erdos536.fiberValue m p := by
  intro hDvd
  have hEq : 5 = 1 :=
    (coprime_five_fiberValue h5m p).eq_one_of_dvd hDvd
  exact (by decide : (5 : Nat) ≠ 1) hEq

/--
Scaling all three vertices of an LCM triangle by the same positive factor
preserves the LCM-triangle property.
-/
theorem scale_is_lcmTriangle
    {q a b c : Nat}
    (hq : 0 < q)
    (htri : Erdos536.IsLcmTriangle a b c) :
    Erdos536.IsLcmTriangle (q * a) (q * b) (q * c) := by
  rcases htri with ⟨hab, hac, hbc, hlab_ac, hlac_bc⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hEq
    apply hab
    exact Nat.mul_left_cancel hq hEq
  · intro hEq
    apply hac
    exact Nat.mul_left_cancel hq hEq
  · intro hEq
    apply hbc
    exact Nat.mul_left_cancel hq hEq
  · calc
      Nat.lcm (q * a) (q * b) = q * Nat.lcm a b := by
        rw [Nat.lcm_mul_left]
      _ = q * Nat.lcm a c := by rw [hlab_ac]
      _ = Nat.lcm (q * a) (q * c) := by
        rw [Nat.lcm_mul_left]
  · calc
      Nat.lcm (q * a) (q * c) = q * Nat.lcm a c := by
        rw [Nat.lcm_mul_left]
      _ = q * Nat.lcm b c := by rw [hlac_bc]
      _ = Nat.lcm (q * b) (q * c) := by
        rw [Nat.lcm_mul_left]

/--
Core 5-adic blocking bridge.

Let `S` be maximal Gamma-free in `D`, and let `c` be a missing board point.
Then there are two old points `u,v ∈ S` such that, for every positive common
scale `q`, the two upper-layer values

    q * (5 * 2^u.i * 3^u.j),  q * (5 * 2^v.i * 3^v.j)

together with the lower-layer value

    q * (2^c.i * 3^c.j)

form an LCM triangle.

Crucially, `q` is arbitrary positive: it may already contain powers of 5.
Thus this applies between every pair of adjacent 5-adic layers, not only
between the bottom two.
-/
theorem maximalGammaFree_blocks_across_five
    {D S : List Erdos536.GridPoint}
    {c : Erdos536.GridPoint}
    {q : Nat}
    (hq : 0 < q)
    (hMax : MaximalGammaFreeIn D S)
    (hcD : c ∈ D)
    (hcS : c ∉ S) :
    ∃ u v : Erdos536.GridPoint,
      u ∈ S ∧
      v ∈ S ∧
      Erdos536.IsLcmTriangle
        (q * (5 * Erdos536.fiberValue 1 u))
        (q * (5 * Erdos536.fiberValue 1 v))
        (q * Erdos536.fiberValue 1 c) := by
  rcases maximalGammaFree_missing_point_has_old_pair hMax hcD hcS with
    ⟨u, v, huS, hvS, hGamma⟩
  refine ⟨u, v, huS, hvS, ?_⟩

  have h5c : ¬ 5 ∣ Erdos536.fiberValue 1 c :=
    not_five_dvd_fiberValue (m := 1) (by decide) c

  rcases hGamma with hCuv | hUcv | hUvc
  ·
    -- c is the Gamma top; u and v are the two old arms.
    rcases Erdos536.gamma_fiberValues_pairwise_distinct
      (m := 1) (by decide : 0 < (1 : Nat)) hCuv with
      ⟨_hCU, _hCV, hUVne⟩
    rcases Erdos536.gamma_pairwise_lcms_eq_top 1 hCuv with
      ⟨hCU, hCV, hUV⟩
    have hCross :
        Erdos536.IsLcmTriangle
          (5 * Erdos536.fiberValue 1 u)
          (5 * Erdos536.fiberValue 1 v)
          (Erdos536.fiberValue 1 c) := by
      apply lift_two_by_five_is_lcmTriangle
        (w := Erdos536.fiberValue 1 c) hUVne hUV
      · simpa [Nat.lcm_comm] using hCU
      · simpa [Nat.lcm_comm] using hCV
      · exact coprime_five_fiberValue (m := 1) (by decide) c
      · exact h5c
    exact scale_is_lcmTriangle hq hCross

  ·
    -- u is the Gamma top, c is the left arm, v is the down arm.
    rcases Erdos536.gamma_fiberValues_pairwise_distinct
      (m := 1) (by decide : 0 < (1 : Nat)) hUcv with
      ⟨_hUC, hUVne, _hCV⟩
    rcases Erdos536.gamma_pairwise_lcms_eq_top 1 hUcv with
      ⟨hUC, hUV, hCV⟩
    have hCross :
        Erdos536.IsLcmTriangle
          (5 * Erdos536.fiberValue 1 u)
          (5 * Erdos536.fiberValue 1 v)
          (Erdos536.fiberValue 1 c) := by
      apply lift_two_by_five_is_lcmTriangle
        (w := Erdos536.fiberValue 1 u) hUVne hUV
      · exact hUC
      · simpa [Nat.lcm_comm] using hCV
      · exact coprime_five_fiberValue (m := 1) (by decide) u
      · exact h5c
    exact scale_is_lcmTriangle hq hCross

  ·
    -- u is the Gamma top, v is the left arm, c is the down arm.
    rcases Erdos536.gamma_fiberValues_pairwise_distinct
      (m := 1) (by decide : 0 < (1 : Nat)) hUvc with
      ⟨hUVne, _hUC, _hVC⟩
    rcases Erdos536.gamma_pairwise_lcms_eq_top 1 hUvc with
      ⟨hUV, hUC, hVC⟩
    have hCross :
        Erdos536.IsLcmTriangle
          (5 * Erdos536.fiberValue 1 u)
          (5 * Erdos536.fiberValue 1 v)
          (Erdos536.fiberValue 1 c) := by
      apply lift_two_by_five_is_lcmTriangle
        (w := Erdos536.fiberValue 1 u) hUVne hUV
      · exact hUC
      · exact hVC
      · exact coprime_five_fiberValue (m := 1) (by decide) u
      · exact h5c
    exact scale_is_lcmTriangle hq hCross


/--
If the upper-layer points of a maximal Gamma-free family are all selected in
the global LCM-triangle-free set `A`, then a missing board point cannot also
be selected in the adjacent lower 5-adic layer.
-/
theorem maximalGammaFree_excludes_lower_selected
    {D S : List Erdos536.GridPoint}
    {A : List Nat}
    {c : Erdos536.GridPoint}
    {q N : Nat}
    (hq : 0 < q)
    (hMax : MaximalGammaFreeIn D S)
    (hcD : c ∈ D)
    (hcS : c ∉ S)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hUpper :
      ∀ p ∈ S,
        q * (5 * Erdos536.fiberValue 1 p) ∈ A) :
    q * Erdos536.fiberValue 1 c ∉ A := by
  intro hcA
  rcases maximalGammaFree_blocks_across_five hq hMax hcD hcS with
    ⟨u, v, huS, hvS, hTri⟩
  exact hA.2.2
    (q * (5 * Erdos536.fiberValue 1 u)) (hUpper u huS)
    (q * (5 * Erdos536.fiberValue 1 v)) (hUpper v hvS)
    (q * Erdos536.fiberValue 1 c) hcA
    hTri

/--
Same blocking statement in Kenta's native `FiberSelectedComplete` language.

If `S` is exactly the selected part of the upper fiber with base `5*q`,
and `S` is maximal Gamma-free in `D`, then every missing point `c ∈ D \ S`
is absent from the adjacent lower fiber with base `q`.
-/
theorem maximalGammaFree_excludes_lower_fiberValue
    {D S : List Erdos536.GridPoint}
    {A : List Nat}
    {c : Erdos536.GridPoint}
    {q N : Nat}
    (hq : 0 < q)
    (hMax : MaximalGammaFreeIn D S)
    (hcD : c ∈ D)
    (hcS : c ∉ S)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete S A (5 * q)) :
    Erdos536.fiberValue q c ∉ A := by
  have hBlock :
      q * Erdos536.fiberValue 1 c ∉ A := by
    apply maximalGammaFree_excludes_lower_selected
      hq hMax hcD hcS hA
    intro p hpS
    have hpA : Erdos536.fiberValue (5 * q) p ∈ A :=
      (hUpperSelected.2 p).1 hpS
    simpa [Erdos536.fiberValue, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hpA
  simpa [Erdos536.fiberValue, Nat.mul_assoc] using hBlock


/-- The origin of the 2,3-exponent grid. -/
def gridOrigin : Erdos536.GridPoint := { i := 0, j := 0 }

/--
For every positive `d ≠ 1` that is coprime to 5, the three numbers
`5`, `5*d`, and `d` form an LCM triangle.
-/
theorem five_five_mul_lower_is_lcmTriangle
    {d : Nat}
    (hd : 0 < d)
    (hd1 : d ≠ 1)
    (h5d : Nat.Coprime 5 d) :
    Erdos536.IsLcmTriangle 5 (5 * d) d := by
  have hAB : Nat.lcm 5 (5 * d) = 5 * d := by
    calc
      Nat.lcm 5 (5 * d) = Nat.lcm (5 * 1) (5 * d) := by simp
      _ = 5 * Nat.lcm 1 d := by rw [Nat.lcm_mul_left]
      _ = 5 * d := by simp
  have hAC : Nat.lcm 5 d = 5 * d := by
    have h := lcm_five_mul_of_lcm_eq
      (a := 1) (c := d) (w := d) (by simp) h5d
    simpa using h
  have hBC : Nat.lcm (5 * d) d = 5 * d := by
    exact Nat.lcm_eq_left (Nat.dvd_mul_left d 5)

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hEq
    have hEq' : 5 * 1 = 5 * d := by simpa using hEq
    have h1d : 1 = d := Nat.mul_left_cancel (by decide : 0 < (5 : Nat)) hEq'
    exact hd1 h1d.symm
  · intro hEq
    have h5dvd : 5 ∣ d := by
      rw [← hEq]
    have h51 : 5 = 1 := h5d.eq_one_of_dvd h5dvd
    exact (by decide : (5 : Nat) ≠ 1) h51
  · intro hEq
    have hEq' : 5 * d = 1 * d := by simpa using hEq
    have h51 : 5 = 1 := Nat.mul_right_cancel hd hEq'
    exact (by decide : (5 : Nat) ≠ 1) h51
  · exact hAB.trans hAC.symm
  · exact hAC.trans hBC.symm

/--
If the origin and a nontrivial point `c` are both selected in an upper
`5*q` fiber, then the corresponding lower `q`-fiber value at `c` is forbidden.
This is the `c ∈ S` half of the blocking dichotomy.
-/
theorem selected_upper_point_excludes_same_lower
    {S : List Erdos536.GridPoint}
    {A : List Nat}
    {c : Erdos536.GridPoint}
    {q N : Nat}
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete S A (5 * q))
    (hOriginS : gridOrigin ∈ S)
    (hcS : c ∈ S)
    (hcNontrivial : Erdos536.fiberValue 1 c ≠ 1) :
    Erdos536.fiberValue q c ∉ A := by
  intro hcLowerA

  have hOriginA : Erdos536.fiberValue (5 * q) gridOrigin ∈ A :=
    (hUpperSelected.2 gridOrigin).1 hOriginS
  have hcUpperA : Erdos536.fiberValue (5 * q) c ∈ A :=
    (hUpperSelected.2 c).1 hcS

  have hdpos : 0 < Erdos536.fiberValue 1 c := by
    simp [Erdos536.fiberValue]
  have h5d : Nat.Coprime 5 (Erdos536.fiberValue 1 c) :=
    coprime_five_fiberValue (m := 1) (by decide) c

  have hBaseTri :
      Erdos536.IsLcmTriangle
        5
        (5 * Erdos536.fiberValue 1 c)
        (Erdos536.fiberValue 1 c) :=
    five_five_mul_lower_is_lcmTriangle hdpos hcNontrivial h5d

  have hScaledTri :
      Erdos536.IsLcmTriangle
        (q * 5)
        (q * (5 * Erdos536.fiberValue 1 c))
        (q * Erdos536.fiberValue 1 c) :=
    scale_is_lcmTriangle hq hBaseTri

  have hTri :
      Erdos536.IsLcmTriangle
        (Erdos536.fiberValue (5 * q) gridOrigin)
        (Erdos536.fiberValue (5 * q) c)
        (Erdos536.fiberValue q c) := by
    simpa [gridOrigin, Erdos536.fiberValue, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using hScaledTri

  exact hA.2.2
    (Erdos536.fiberValue (5 * q) gridOrigin) hOriginA
    (Erdos536.fiberValue (5 * q) c) hcUpperA
    (Erdos536.fiberValue q c) hcLowerA
    hTri

/--
Pointwise blocking dichotomy for an adjacent pair of 5-adic layers.

Assume:
* `S` is exactly the selected upper `5*q` fiber,
* `S` is maximal Gamma-free in `D`,
* the origin is selected.

Then every nontrivial point `c ∈ D` is absent from the lower `q` fiber,
whether `c` belongs to the upper slice or not.
-/
theorem maximalGammaFree_blocks_every_nontrivial_lower_point
    {D S : List Erdos536.GridPoint}
    {A : List Nat}
    {c : Erdos536.GridPoint}
    {q N : Nat}
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hMax : MaximalGammaFreeIn D S)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete S A (5 * q))
    (hOriginS : gridOrigin ∈ S)
    (hcD : c ∈ D)
    (hcNontrivial : Erdos536.fiberValue 1 c ≠ 1) :
    Erdos536.fiberValue q c ∉ A := by
  by_cases hcS : c ∈ S
  · exact selected_upper_point_excludes_same_lower
      hq hA hUpperSelected hOriginS hcS hcNontrivial
  · exact maximalGammaFree_excludes_lower_fiberValue
      hq hMax hcD hcS hA hUpperSelected


/--
A maximum-cardinality Gamma-free family inside `D`.
-/
def MaximumGammaFreeIn
    (D S : List Erdos536.GridPoint) : Prop :=
  Erdos536.GammaFree S ∧
    S.Subset D ∧
    ∀ T : List Erdos536.GridPoint,
      Erdos536.GammaFree T →
      T.Subset D →
      T.length ≤ S.length

/-- The origin can never be the top vertex of a Gamma-pattern. -/
theorem no_gamma_with_origin_as_top
    {left down : Erdos536.GridPoint} :
    ¬ Erdos536.GammaPattern gridOrigin left down := by
  intro h
  rcases h with ⟨_hRow, hLeftLt, _hCol, _hDownLt⟩
  simp [gridOrigin] at hLeftLt

/-- The origin can never be the left vertex of a Gamma-pattern. -/
theorem no_gamma_with_origin_as_left
    {top down : Erdos536.GridPoint} :
    ¬ Erdos536.GammaPattern top gridOrigin down := by
  intro h
  rcases h with ⟨hRow, _hLeftLt, _hCol, hDownLt⟩
  have hTopJ : top.j = 0 := by
    simpa [gridOrigin] using hRow.symm
  rw [hTopJ] at hDownLt
  omega

/-- The origin can never be the down vertex of a Gamma-pattern. -/
theorem no_gamma_with_origin_as_down
    {top left : Erdos536.GridPoint} :
    ¬ Erdos536.GammaPattern top left gridOrigin := by
  intro h
  rcases h with ⟨_hRow, hLeftLt, hCol, _hDownLt⟩
  have hTopI : top.i = 0 := by
    simpa [gridOrigin] using hCol.symm
  rw [hTopI] at hLeftLt
  omega

/--
Adjoining the origin to a Gamma-free family remains Gamma-free.
-/
theorem gammaFree_cons_origin
    {S : List Erdos536.GridPoint}
    (hGF : Erdos536.GammaFree S)
    (hOriginNot : gridOrigin ∉ S) :
    Erdos536.GammaFree (gridOrigin :: S) := by
  constructor
  · exact List.nodup_cons.mpr ⟨hOriginNot, hGF.1⟩
  · intro top hTop left hLeft down hDown hGamma
    rcases List.mem_cons.mp hTop with hTop0 | hTopS
    · subst top
      exact no_gamma_with_origin_as_top hGamma
    rcases List.mem_cons.mp hLeft with hLeft0 | hLeftS
    · subst left
      exact no_gamma_with_origin_as_left hGamma
    rcases List.mem_cons.mp hDown with hDown0 | hDownS
    · subst down
      exact no_gamma_with_origin_as_down hGamma
    · exact hGF.2 top hTopS left hLeftS down hDownS hGamma

/--
A maximum-cardinality Gamma-free family is inclusion-maximal.
-/
theorem maximumGammaFree_is_maximal
    {D S : List Erdos536.GridPoint}
    (hMaximum : MaximumGammaFreeIn D S) :
    MaximalGammaFreeIn D S := by
  rcases hMaximum with ⟨hGF, hSubset, hCard⟩
  refine ⟨hGF, ?_⟩
  intro c hcD hcS
  intro hGFcons
  have hSubsetCons : (c :: S).Subset D := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxS
    · exact hcD
    · exact hSubset hxS
  have hLen := hCard (c :: S) hGFcons hSubsetCons
  simp at hLen

/--
If the ambient board contains the origin, then every maximum-cardinality
Gamma-free family contains the origin.
-/
theorem maximumGammaFree_contains_origin
    {D S : List Erdos536.GridPoint}
    (hOriginD : gridOrigin ∈ D)
    (hMaximum : MaximumGammaFreeIn D S) :
    gridOrigin ∈ S := by
  rcases hMaximum with ⟨hGF, hSubset, hCard⟩
  by_contra hOriginS
  have hGFcons : Erdos536.GammaFree (gridOrigin :: S) :=
    gammaFree_cons_origin hGF hOriginS
  have hSubsetCons : (gridOrigin :: S).Subset D := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxS
    · exact hOriginD
    · exact hSubset hxS
  have hLen := hCard (gridOrigin :: S) hGFcons hSubsetCons
  simp at hLen

/--
For a maximum-cardinality Gamma-free upper slice, the two structural
hypotheses needed by the pointwise blocking theorem are automatic.
-/
theorem maximumGammaFree_origin_and_maximal
    {D S : List Erdos536.GridPoint}
    (hOriginD : gridOrigin ∈ D)
    (hMaximum : MaximumGammaFreeIn D S) :
    gridOrigin ∈ S ∧ MaximalGammaFreeIn D S := by
  exact ⟨
    maximumGammaFree_contains_origin hOriginD hMaximum,
    maximumGammaFree_is_maximal hMaximum
  ⟩

/--
Blocking theorem with the natural extremality hypothesis.

If the selected upper `5*q` slice is maximum-cardinality Gamma-free inside
`D`, and `D` contains the origin, then every nontrivial point of `D` is
forbidden in the adjacent lower `q` slice.
-/
theorem maximumGammaFree_blocks_every_nontrivial_lower_point
    {D S : List Erdos536.GridPoint}
    {A : List Nat}
    {c : Erdos536.GridPoint}
    {q N : Nat}
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete S A (5 * q))
    (hOriginD : gridOrigin ∈ D)
    (hMaximum : MaximumGammaFreeIn D S)
    (hcD : c ∈ D)
    (hcNontrivial : Erdos536.fiberValue 1 c ≠ 1) :
    Erdos536.fiberValue q c ∉ A := by
  rcases maximumGammaFree_origin_and_maximal hOriginD hMaximum with
    ⟨hOriginS, hMaximal⟩
  exact maximalGammaFree_blocks_every_nontrivial_lower_point
    hq hA hMaximal hUpperSelected hOriginS hcD hcNontrivial


/-!
## The factor-5 annulus

The blocking lemma says that, when the upper 5-adic slice is extremal,
the adjacent lower slice can contain no nontrivial point from the inner
board.  What remains is the multiplicative annulus

    T/5 < 2^i 3^j ≤ T.

For natural-number bookkeeping it is convenient to encode the lower
inequality without division as

    T < 5 * (2^i 3^j).

This is the same factor-5 window that is used in the hand proof.
-/

/-- Membership in the factor-5 annulus at scale `T`. -/
def InFiveAnnulus
    (T : Nat)
    (p : Erdos536.GridPoint) : Prop :=
  Erdos536.fiberValue 1 p ≤ T ∧
    T < 5 * Erdos536.fiberValue 1 p

/--
Finite list of all 2,3-smooth exponent points in the factor-5 annulus.
We obtain it by filtering Kenta's complete fiber-region list.
-/
def FiveAnnulusList (T : Nat) : List Erdos536.GridPoint :=
  (Erdos536.FiberRegionList 1 T).filter
    (fun p => decide (T < 5 * Erdos536.fiberValue 1 p))

/-- The finite annulus list has no duplicate grid points. -/
theorem fiveAnnulusList_nodup (T : Nat) :
    (FiveAnnulusList T).Nodup := by
  exact
    (Erdos536.fiberRegionList_nodup 1 T).filter
      (fun p => decide (T < 5 * Erdos536.fiberValue 1 p))

/-- Exact membership characterization of the finite annulus list. -/
theorem mem_fiveAnnulusList
    {T : Nat}
    {p : Erdos536.GridPoint} :
    p ∈ FiveAnnulusList T ↔ InFiveAnnulus T p := by
  constructor
  · intro hp
    rcases List.mem_filter.mp hp with ⟨hpRegion, hpWindow⟩
    have hpUpper : Erdos536.fiberValue 1 p ≤ T :=
      (Erdos536.fiberRegionList_complete
        (m := 1) (N := T) (by decide : 0 < (1 : Nat)) p).1 hpRegion
    exact ⟨hpUpper, by simpa using hpWindow⟩
  · intro hp
    rcases hp with ⟨hpUpper, hpWindow⟩
    apply List.mem_filter.mpr
    constructor
    · exact
        (Erdos536.fiberRegionList_complete
          (m := 1) (N := T) (by decide : 0 < (1 : Nat)) p).2 hpUpper
    · simpa using hpWindow

/-- Every annulus point lies in the ordinary fiber region at scale `T`. -/
theorem fiveAnnulusList_subset_fiberRegion (T : Nat) :
    (FiveAnnulusList T).Subset (Erdos536.FiberRegionList 1 T) := by
  intro p hp
  exact (List.mem_filter.mp hp).1

/--
For `T ≥ 5`, the origin is not in the factor-5 annulus.
This is the formal version of the fact that the blocking theorem leaves
the origin as one exceptional lower-slice point, separate from the annulus.
-/
theorem gridOrigin_not_mem_fiveAnnulus
    {T : Nat}
    (hT : 5 ≤ T) :
    gridOrigin ∉ FiveAnnulusList T := by
  intro hOrigin
  have hAnn : InFiveAnnulus T gridOrigin :=
    (mem_fiveAnnulusList).1 hOrigin
  rcases hAnn with ⟨_hUpper, hWindow⟩
  simp [gridOrigin, Erdos536.fiberValue] at hWindow
  omega

/-- Every point in the factor-5 annulus has positive 2,3-smooth value. -/
theorem fiveAnnulus_value_pos
    {T : Nat}
    {p : Erdos536.GridPoint}
    (_hp : InFiveAnnulus T p) :
    0 < Erdos536.fiberValue 1 p := by
  simp [Erdos536.fiberValue]

/--
Pure arithmetic form of the factor-5 obstruction: a number in the annulus
cannot coexist below `T` with another number at least six times as large.
The large-scale row/column spacing lemmas will reduce to this statement.
-/
theorem factor_five_window_forbids_sixfold
    {T x y : Nat}
    (hWindow : T < 5 * x)
    (hyT : y ≤ T)
    (hSix : 6 * x ≤ y) :
    False := by
  omega


/--
If two grid points have the same 2-exponent and their 3-exponents differ
by at least two, then the larger value is at least nine times the smaller.
-/
theorem nine_mul_fiberValue_le_of_same_i_gap_two
    {p q : Erdos536.GridPoint}
    (hi : p.i = q.i)
    (hGap : p.j + 2 ≤ q.j) :
    9 * Erdos536.fiberValue 1 p ≤ Erdos536.fiberValue 1 q := by
  have hPow : 3 ^ (p.j + 2) ≤ 3 ^ q.j :=
    Nat.pow_le_pow_right (by decide : 0 < (3 : Nat)) hGap
  calc
    9 * Erdos536.fiberValue 1 p
        = (2 ^ p.i) * 3 ^ (p.j + 2) := by
            simp only [Erdos536.fiberValue, one_mul, pow_add]
            norm_num
            ring
    _ ≤ (2 ^ p.i) * 3 ^ q.j :=
      Nat.mul_le_mul_left (2 ^ p.i) hPow
    _ = Erdos536.fiberValue 1 q := by
      simp [Erdos536.fiberValue, hi]

/--
Two points in the factor-5 annulus with the same 2-exponent cannot have
3-exponents separated by two or more.

This is the formal version of the elementary observation

    3^2 = 9 > 5,

so a multiplicative interval of width 5 contains at most two consecutive
powers of 3 once the power of 2 is fixed.
-/
theorem fiveAnnulus_same_i_forbids_j_gap_two
    {T : Nat}
    {p q : Erdos536.GridPoint}
    (hp : InFiveAnnulus T p)
    (hq : InFiveAnnulus T q)
    (hi : p.i = q.i) :
    ¬ p.j + 2 ≤ q.j := by
  intro hGap
  have hNine :
      9 * Erdos536.fiberValue 1 p ≤ Erdos536.fiberValue 1 q :=
    nine_mul_fiberValue_le_of_same_i_gap_two hi hGap
  have hSix :
      6 * Erdos536.fiberValue 1 p ≤ Erdos536.fiberValue 1 q := by
    exact Nat.le_trans (by omega) hNine
  exact factor_five_window_forbids_sixfold hp.2 hq.1 hSix

/--
Ordered form of the preceding spacing statement: with the same 2-exponent,
two annulus points have 3-exponents differing by at most one.
-/
theorem fiveAnnulus_same_i_j_le_add_one
    {T : Nat}
    {p q : Erdos536.GridPoint}
    (hp : InFiveAnnulus T p)
    (hq : InFiveAnnulus T q)
    (hi : p.i = q.i)
    (hjq : p.j ≤ q.j) :
    q.j ≤ p.j + 1 := by
  have hNoGap :=
    fiveAnnulus_same_i_forbids_j_gap_two hp hq hi
  omega

end Erdos536813
