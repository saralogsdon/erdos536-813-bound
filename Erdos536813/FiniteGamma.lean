import Erdos536813.AnnulusTheory

namespace Erdos536813

/-!
## Executable finite Gamma-freeness checker

The remaining annulus range `120 ≤ T ≤ 728` is finite.  We use an explicit
Boolean implementation of the four coordinate conditions defining a
Gamma-pattern, rather than asking typeclass inference for decidability of the
imported proposition.
-/

/-- Executable Boolean version of `Erdos536.GammaPattern`. -/
def GammaPatternBool
    (top left down : Erdos536.GridPoint) : Bool :=
  decide (left.j = top.j) &&
    decide (left.i < top.i) &&
    decide (down.i = top.i) &&
    decide (down.j < top.j)

/-- The Boolean Gamma-pattern test is exactly the mathematical predicate. -/
theorem gammaPatternBool_eq_true_iff
    (top left down : Erdos536.GridPoint) :
    GammaPatternBool top left down = true ↔
      Erdos536.GammaPattern top left down := by
  simp [GammaPatternBool, Erdos536.GammaPattern, and_assoc]

/--
Executable check that a finite list is nodup and contains no Gamma-pattern.
-/
def GammaFreeFiniteBool (S : List Erdos536.GridPoint) : Bool :=
  decide S.Nodup &&
    S.all (fun top =>
      S.all (fun left =>
        S.all (fun down =>
          ! GammaPatternBool top left down)))

/-- The executable checker exactly matches `Erdos536.GammaFree`. -/
theorem gammaFreeFiniteBool_eq_true_iff
    (S : List Erdos536.GridPoint) :
    GammaFreeFiniteBool S = true ↔ Erdos536.GammaFree S := by
  constructor
  · intro h
    have h' :
        S.Nodup ∧
          ∀ top ∈ S, ∀ left ∈ S, ∀ down ∈ S,
            GammaPatternBool top left down = false := by
      simpa [GammaFreeFiniteBool] using h
    refine ⟨h'.1, ?_⟩
    intro top hTop left hLeft down hDown hPat
    have hTrue : GammaPatternBool top left down = true :=
      (gammaPatternBool_eq_true_iff top left down).2 hPat
    have hFalse := h'.2 top hTop left hLeft down hDown
    simp [hTrue] at hFalse
  · intro h
    have hNo :
        ∀ top ∈ S, ∀ left ∈ S, ∀ down ∈ S,
          GammaPatternBool top left down = false := by
      intro top hTop left hLeft down hDown
      cases hBool : GammaPatternBool top left down with
      | false => rfl
      | true =>
          exfalso
          exact h.2 top hTop left hLeft down hDown
            ((gammaPatternBool_eq_true_iff top left down).1 hBool)
    simpa [GammaFreeFiniteBool] using And.intro h.1 hNo

/-- Soundness form convenient for computational certificates. -/
theorem gammaFree_of_gammaFreeFiniteBool
    {S : List Erdos536.GridPoint}
    (h : GammaFreeFiniteBool S = true) :
    Erdos536.GammaFree S :=
  (gammaFreeFiniteBool_eq_true_iff S).1 h

/-- Completeness form convenient for computational certificates. -/
theorem gammaFreeFiniteBool_of_gammaFree
    {S : List Erdos536.GridPoint}
    (h : Erdos536.GammaFree S) :
    GammaFreeFiniteBool S = true :=
  (gammaFreeFiniteBool_eq_true_iff S).2 h

/-- Basic kernel-checked sanity checks for the executable predicate. -/
example : GammaFreeFiniteBool ([] : List Erdos536.GridPoint) = true := by
  native_decide

example :
    GammaFreeFiniteBool
      [({ i := 1, j := 1 } : Erdos536.GridPoint),
       ({ i := 0, j := 1 } : Erdos536.GridPoint),
       ({ i := 1, j := 0 } : Erdos536.GridPoint)] = false := by
  native_decide


/-!
## Sound finite subset-bound certificates

A finite Boolean certificate checks every sublist of a finite ambient list.
For a mathematical Gamma-free set represented by any nodup list `S ⊆ D`,
`S.Nodup` gives a sub-permutation into `D`; hence `S` is permutation-equivalent
to an actual sublist of `D`. Since Gamma-freeness is invariant under
permutation, checking all sublists is sufficient.
-/

/-- Gamma-freeness depends only on the underlying finite set, not list order. -/
theorem gammaFree_of_perm
    {S U : List Erdos536.GridPoint}
    (hPerm : List.Perm U S)
    (hS : Erdos536.GammaFree S) :
    Erdos536.GammaFree U := by
  constructor
  · exact hPerm.nodup_iff.mpr hS.1
  · intro top hTop left hLeft down hDown hPat
    have hTopS : top ∈ S := hPerm.mem_iff.mp hTop
    have hLeftS : left ∈ S := hPerm.mem_iff.mp hLeft
    have hDownS : down ∈ S := hPerm.mem_iff.mp hDown
    exact hS.2 top hTopS left hLeftS down hDownS hPat

/--
Boolean certificate asserting that every Gamma-free sublist of `D`
has length at most `B`.
-/
def GammaFreeSubsetBoundBool
    (D : List Erdos536.GridPoint)
    (B : Nat) : Bool :=
  D.sublists.all (fun U =>
    (! GammaFreeFiniteBool U) || decide (U.length ≤ B))

/--
Soundness of the exhaustive finite certificate.

This bridges a `native_decide` computation over all sublists to every
mathematical Gamma-free nodup subset, regardless of list ordering.
-/
theorem gammaFree_length_le_of_subsetBoundBool
    {D S : List Erdos536.GridPoint}
    {B : Nat}
    (hCert : GammaFreeSubsetBoundBool D B = true)
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset D) :
    S.length ≤ B := by
  have hSubperm : List.Subperm S D :=
    hGamma.1.subperm hSub
  rcases hSubperm with ⟨U, hPerm, hUSub⟩
  have hUMem : U ∈ D.sublists := by
    exact List.mem_sublists.mpr hUSub
  have hUGamma : Erdos536.GammaFree U :=
    gammaFree_of_perm hPerm hGamma
  have hUBool : GammaFreeFiniteBool U = true :=
    gammaFreeFiniteBool_of_gammaFree hUGamma
  have hAll :
      ∀ V ∈ D.sublists,
        ((! GammaFreeFiniteBool V) || decide (V.length ≤ B)) = true := by
    simpa [GammaFreeSubsetBoundBool] using hCert
  have hUCheck := hAll U hUMem
  rw [hUBool] at hUCheck
  have hULe : U.length ≤ B := by
    simpa using hUCheck
  simpa [hPerm.length_eq] using hULe

/-- Tiny sanity check for the finite certificate mechanism. -/
example :
    GammaFreeSubsetBoundBool
      [({ i := 1, j := 1 } : Erdos536.GridPoint),
       ({ i := 0, j := 1 } : Erdos536.GridPoint),
       ({ i := 1, j := 0 } : Erdos536.GridPoint)]
      2 = true := by
  native_decide

end Erdos536813
