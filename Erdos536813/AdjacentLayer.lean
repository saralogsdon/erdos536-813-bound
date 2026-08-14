import Erdos536813.AnnulusFinite

namespace Erdos536813

/-!
## Adjacent 5-adic layers: an extremal upper slice forces two units of lower deficit

We now combine the pointwise blocking theorem with the strong annulus lemma.
For a lower scale `T`, the points satisfying

    5 * 2^i * 3^j ≤ T

form the inner board corresponding to the adjacent upper 5-adic layer.
If that upper selected slice is maximum-cardinality Gamma-free, every
non-origin selected point in the lower slice is forced outside the inner
board, hence into the factor-5 annulus.  The annulus has deficit at least
three; allowing the origin back costs at most one point, leaving a net
lower-slice deficit of at least two.
-/

/-- The inner board corresponding to the adjacent upper 5-adic layer. -/
def FiveInnerBoardList (T : Nat) : List Erdos536.GridPoint :=
  (Erdos536.FiberRegionList 1 T).filter
    (fun p => decide (5 * Erdos536.fiberValue 1 p ≤ T))

/-- Exact membership characterization of the inner board. -/
theorem mem_fiveInnerBoardList
    {T : Nat}
    {p : Erdos536.GridPoint} :
    p ∈ FiveInnerBoardList T ↔
      5 * Erdos536.fiberValue 1 p ≤ T := by
  constructor
  · intro hp
    have hBool := (List.mem_filter.mp hp).2
    simpa using hBool
  · intro hp
    apply List.mem_filter.mpr
    constructor
    · have hpRegion : Erdos536.fiberValue 1 p ≤ T := by
        have hpPos : 0 < Erdos536.fiberValue 1 p := by
          simp [Erdos536.fiberValue]
        omega
      exact
        (Erdos536.fiberRegionList_complete
          (m := 1) (N := T) (by decide : 0 < (1 : Nat)) p).2 hpRegion
    · simpa using hp

/-- The origin lies in the inner board as soon as `5 ≤ T`. -/
theorem gridOrigin_mem_fiveInnerBoardList
    {T : Nat}
    (hT : 5 ≤ T) :
    gridOrigin ∈ FiveInnerBoardList T := by
  apply (mem_fiveInnerBoardList).2
  simpa [gridOrigin, Erdos536.fiberValue] using hT

/-- In the `m = 1` fiber, value `1` occurs only at the grid origin. -/
theorem fiberValue_one_eq_one_iff
    (p : Erdos536.GridPoint) :
    Erdos536.fiberValue 1 p = 1 ↔ p = gridOrigin := by
  cases p with
  | mk i j =>
      simp [Erdos536.fiberValue, gridOrigin]

/-- Erasing one point can decrease the length by at most one. -/
theorem length_le_erase_add_one
    (S : List Erdos536.GridPoint)
    (p : Erdos536.GridPoint) :
    S.length ≤ (S.erase p).length + 1 := by
  have h := List.le_length_erase
    (l := S) (a := p)
  omega

/-- Gamma-freeness is inherited by erasing a point. -/
theorem gammaFree_erase
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (p : Erdos536.GridPoint) :
    Erdos536.GammaFree (S.erase p) := by
  constructor
  · exact hGamma.1.erase p
  · intro top hTop left hLeft down hDown hPat
    exact hGamma.2
      top (List.erase_subset hTop)
      left (List.erase_subset hLeft)
      down (List.erase_subset hDown)
      hPat

/--
Main adjacent-layer saving lemma.

Assume `T ≥ 120`.  Let `Upper` be exactly the selected `5*q` fiber and
`Lower` exactly the selected `q` fiber of an ambient LCM-triangle-free set.
If `Upper` is maximum-cardinality Gamma-free in the inner board and every
selected lower point has `2^i 3^j ≤ T`, then the lower slice misses at least
two points relative to the ordinary one-slice benchmark `L23 T`.
-/
theorem maximum_upper_forces_lower_deficit_two
    {T q N : Nat}
    {A : List Nat}
    {Upper Lower : List Erdos536.GridPoint}
    (hT : 120 ≤ T)
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete Upper A (5 * q))
    (hUpperMaximum :
      MaximumGammaFreeIn (FiveInnerBoardList T) Upper)
    (hLowerSelected :
      Erdos536.FiberSelectedComplete Lower A q)
    (hLowerBound :
      ∀ p ∈ Lower, Erdos536.fiberValue 1 p ≤ T) :
    Lower.length + 2 ≤ L23 T := by
  have hOriginInner : gridOrigin ∈ FiveInnerBoardList T := by
    apply gridOrigin_mem_fiveInnerBoardList
    omega

  have hLowerGamma : Erdos536.GammaFree Lower :=
    Erdos536.fiberSelected_gammaFree hq hA hLowerSelected

  have hEraseGamma : Erdos536.GammaFree (Lower.erase gridOrigin) :=
    gammaFree_erase hLowerGamma gridOrigin

  have hEraseAnnulus :
      ∀ p ∈ Lower.erase gridOrigin, InFiveAnnulus T p := by
    intro p hpErase
    have hpEraseInfo :
        p ≠ gridOrigin ∧ p ∈ Lower :=
      (hLowerGamma.1.mem_erase_iff).1 hpErase
    have hpNeOrigin : p ≠ gridOrigin :=
      hpEraseInfo.1
    have hpLower : p ∈ Lower :=
      hpEraseInfo.2
    have hpSelected : Erdos536.fiberValue q p ∈ A :=
      (hLowerSelected.2 p).1 hpLower
    have hpNontrivial : Erdos536.fiberValue 1 p ≠ 1 := by
      intro hpOne
      apply hpNeOrigin
      exact (fiberValue_one_eq_one_iff p).1 hpOne
    have hpUpperBound : Erdos536.fiberValue 1 p ≤ T :=
      hLowerBound p hpLower
    have hpWindow : T < 5 * Erdos536.fiberValue 1 p := by
      by_contra hNotWindow
      have hpInnerIneq : 5 * Erdos536.fiberValue 1 p ≤ T :=
        Nat.le_of_not_gt hNotWindow
      have hpInner : p ∈ FiveInnerBoardList T :=
        (mem_fiveInnerBoardList).2 hpInnerIneq
      have hpForbidden : Erdos536.fiberValue q p ∉ A :=
        maximumGammaFree_blocks_every_nontrivial_lower_point
          hq hA hUpperSelected hOriginInner hUpperMaximum
          hpInner hpNontrivial
      exact hpForbidden hpSelected
    exact ⟨hpUpperBound, hpWindow⟩

  have hAnnulusBound :
      (Lower.erase gridOrigin).length + 3 ≤ L23 T :=
    gammaFree_annulus_deficit_three
      hT hEraseGamma hEraseAnnulus

  have hRestore :
      Lower.length ≤ (Lower.erase gridOrigin).length + 1 :=
    length_le_erase_add_one Lower gridOrigin

  omega

end Erdos536813
