import Erdos536813.TwoLayerCore

namespace Erdos536813


/-!
## Fast exact two-layer certificates

The original exact certificate recomputed a full ordered-triple LCM search
inside every candidate pair.  For the larger finite boards this is wasteful.

For a fixed pair of ambient boards we instead precompute every cross-layer
LCM-triangle witness of the form

    one lower point + two upper points,

and then each near-extremal candidate pair only checks whether it contains one
of those already-computed witnesses.

This is a sound certificate even without proving that every possible
two-layer triangle has this form: if the Boolean certificate returns `true`,
it has explicitly found an actual forbidden LCM triangle in every candidate
pair that could violate the desired deficit bound.
-/

/-- A lower point together with two upper points. -/
abbrev CrossWitness :=
  Erdos536.GridPoint ×
    (Erdos536.GridPoint × Erdos536.GridPoint)

/--
All ambient cross-layer triples that are actual LCM triangles before applying
the common positive scale.
-/
def CrossWitnesses
    (Dlow Dup : List Erdos536.GridPoint) :
    List CrossWitness :=
  (Dlow.product (Dup.product Dup)).filter (fun w =>
    IsLcmTriangleBool
      (Erdos536.fiberValue 1 w.1)
      (5 * Erdos536.fiberValue 1 w.2.1)
      (5 * Erdos536.fiberValue 1 w.2.2))

/-- Membership-only test: does a candidate pair contain this witness? -/
def CrossWitnessPresentBool
    (W : List CrossWitness)
    (Lower Upper : List Erdos536.GridPoint) : Bool :=
  W.any (fun w =>
    decide (w.1 ∈ Lower) &&
      decide (w.2.1 ∈ Upper) &&
      decide (w.2.2 ∈ Upper))

theorem crossWitnessPresentBool_eq_true_iff
    (W : List CrossWitness)
    (Lower Upper : List Erdos536.GridPoint) :
    CrossWitnessPresentBool W Lower Upper = true ↔
      ∃ w ∈ W,
        w.1 ∈ Lower ∧
        w.2.1 ∈ Upper ∧
        w.2.2 ∈ Upper := by
  simp [CrossWitnessPresentBool, and_assoc]

/-- Every precomputed witness is an actual LCM triangle. -/
theorem crossWitness_is_lcmTriangle
    {Dlow Dup : List Erdos536.GridPoint}
    {w : CrossWitness}
    (hw : w ∈ CrossWitnesses Dlow Dup) :
    Erdos536.IsLcmTriangle
      (Erdos536.fiberValue 1 w.1)
      (5 * Erdos536.fiberValue 1 w.2.1)
      (5 * Erdos536.fiberValue 1 w.2.2) := by
  have hBool := (List.mem_filter.mp hw).2
  apply (isLcmTriangleBool_eq_true_iff
    (Erdos536.fiberValue 1 w.1)
    (5 * Erdos536.fiberValue 1 w.2.1)
    (5 * Erdos536.fiberValue 1 w.2.2)).1
  simpa using hBool

/--
For one candidate pair, either the desired deficit is already present, or the
pair must contain one of the precomputed cross-layer witnesses.
-/
def FastTwoLayerPairDeficitCheck
    (W : List CrossWitness)
    (Llow Lup : Nat)
    (Lower Upper : List Erdos536.GridPoint) : Bool :=
  if Lower.length + Upper.length + 2 ≤ Llow + Lup then
    true
  else
    CrossWitnessPresentBool W Lower Upper

/--
Fast executable certificate.

The three expensive board-dependent objects are deliberately hoisted outside
the nested candidate loops so native evaluation computes each only once:
the near-extremal lower families, the near-extremal upper families, and the
ambient cross-witness list.
-/
def FastTwoLayerDeficitTwoCertificate
    (Dlow Dup : List Erdos536.GridPoint)
    (Llow Lup : Nat) : Bool :=
  let lowerFamilies :=
    NearExtremalGammaFreeFamilies Dlow (Llow - 1)
  let upperFamilies :=
    NearExtremalGammaFreeFamilies Dup (Lup - 1)
  let witnesses :=
    CrossWitnesses Dlow Dup
  lowerFamilies.all (fun Lower =>
    upperFamilies.all (fun Upper =>
      FastTwoLayerPairDeficitCheck
        witnesses Llow Lup Lower Upper))

/-- Soundness of the optimized finite certificate. -/
theorem fast_twoLayer_deficit_two_of_certificate
    {Dlow Dup Lower Upper : List Erdos536.GridPoint}
    {Llow Lup : Nat}
    (hLlow : 1 ≤ Llow)
    (hLup : 1 ≤ Lup)
    (hCert :
      FastTwoLayerDeficitTwoCertificate
        Dlow Dup Llow Lup = true)
    (hLowerGamma : Erdos536.GammaFree Lower)
    (hLowerSub : Lower.Subset Dlow)
    (hLowerBound : Lower.length ≤ Llow)
    (hUpperGamma : Erdos536.GammaFree Upper)
    (hUpperSub : Upper.Subset Dup)
    (hUpperBound : Upper.length ≤ Lup)
    (hFree : TwoLayerTriangleFree Lower Upper) :
    Lower.length + Upper.length + 2 ≤ Llow + Lup := by
  by_contra hGoal

  have hNearLower : Llow - 1 ≤ Lower.length := by
    omega
  have hNearUpper : Lup - 1 ≤ Upper.length := by
    omega

  have hLowerSubperm : List.Subperm Lower Dlow :=
    hLowerGamma.1.subperm hLowerSub
  rcases hLowerSubperm with
    ⟨Lower', hLowerPerm, hLowerSublist⟩
  have hLowerMem : Lower' ∈ Dlow.sublists :=
    List.mem_sublists.mpr hLowerSublist
  have hLowerGamma' : Erdos536.GammaFree Lower' :=
    gammaFree_of_perm hLowerPerm hLowerGamma
  have hLowerGammaBool :
      GammaFreeFiniteBool Lower' = true :=
    gammaFreeFiniteBool_of_gammaFree hLowerGamma'
  have hLowerLenEq : Lower'.length = Lower.length :=
    hLowerPerm.length_eq
  have hLowerNear' : Llow - 1 ≤ Lower'.length := by
    omega
  have hLowerCand :
      Lower' ∈
        NearExtremalGammaFreeFamilies
          Dlow (Llow - 1) := by
    apply List.mem_filter.mpr
    constructor
    · exact hLowerMem
    · simp [hLowerGammaBool, hLowerNear']

  have hUpperSubperm : List.Subperm Upper Dup :=
    hUpperGamma.1.subperm hUpperSub
  rcases hUpperSubperm with
    ⟨Upper', hUpperPerm, hUpperSublist⟩
  have hUpperMem : Upper' ∈ Dup.sublists :=
    List.mem_sublists.mpr hUpperSublist
  have hUpperGamma' : Erdos536.GammaFree Upper' :=
    gammaFree_of_perm hUpperPerm hUpperGamma
  have hUpperGammaBool :
      GammaFreeFiniteBool Upper' = true :=
    gammaFreeFiniteBool_of_gammaFree hUpperGamma'
  have hUpperLenEq : Upper'.length = Upper.length :=
    hUpperPerm.length_eq
  have hUpperNear' : Lup - 1 ≤ Upper'.length := by
    omega
  have hUpperCand :
      Upper' ∈
        NearExtremalGammaFreeFamilies
          Dup (Lup - 1) := by
    apply List.mem_filter.mpr
    constructor
    · exact hUpperMem
    · simp [hUpperGammaBool, hUpperNear']

  have hAll :
      ∀ L ∈ NearExtremalGammaFreeFamilies
          Dlow (Llow - 1),
        ∀ U ∈ NearExtremalGammaFreeFamilies
            Dup (Lup - 1),
          FastTwoLayerPairDeficitCheck
            (CrossWitnesses Dlow Dup)
            Llow Lup L U = true := by
    simpa [FastTwoLayerDeficitTwoCertificate] using hCert

  have hPair :=
    hAll Lower' hLowerCand Upper' hUpperCand

  have hTooBig' :
      ¬ (Lower'.length + Upper'.length + 2 ≤
          Llow + Lup) := by
    omega

  have hWitnessBool :
      CrossWitnessPresentBool
        (CrossWitnesses Dlow Dup)
        Lower' Upper' = true := by
    simpa [FastTwoLayerPairDeficitCheck, hTooBig']
      using hPair

  rcases
      (crossWitnessPresentBool_eq_true_iff
        (CrossWitnesses Dlow Dup)
        Lower' Upper').1 hWitnessBool with
    ⟨w, hwW, hwLower, hwUpper₁, hwUpper₂⟩

  have hTri :
      Erdos536.IsLcmTriangle
        (Erdos536.fiberValue 1 w.1)
        (5 * Erdos536.fiberValue 1 w.2.1)
        (5 * Erdos536.fiberValue 1 w.2.2) :=
    crossWitness_is_lcmTriangle hwW

  have hFree' :
      TwoLayerTriangleFree Lower' Upper' :=
    twoLayerTriangleFree_of_perm
      hLowerPerm hUpperPerm hFree

  have hLowerVal :
      Erdos536.fiberValue 1 w.1 ∈
        TwoLayerValues Lower' Upper' := by
    rw [TwoLayerValues]
    apply List.mem_append.mpr
    exact Or.inl
      (List.mem_map.mpr ⟨w.1, hwLower, rfl⟩)

  have hUpperVal₁ :
      5 * Erdos536.fiberValue 1 w.2.1 ∈
        TwoLayerValues Lower' Upper' := by
    rw [TwoLayerValues]
    apply List.mem_append.mpr
    exact Or.inr
      (List.mem_map.mpr
        ⟨w.2.1, hwUpper₁, rfl⟩)

  have hUpperVal₂ :
      5 * Erdos536.fiberValue 1 w.2.2 ∈
        TwoLayerValues Lower' Upper' := by
    rw [TwoLayerValues]
    apply List.mem_append.mpr
    exact Or.inr
      (List.mem_map.mpr
        ⟨w.2.2, hwUpper₂, rfl⟩)

  exact hFree'
    (Erdos536.fiberValue 1 w.1) hLowerVal
    (5 * Erdos536.fiberValue 1 w.2.1) hUpperVal₁
    (5 * Erdos536.fiberValue 1 w.2.2) hUpperVal₂
    hTri

/--
Selected-fiber consequence of a fast concrete certificate.
-/
theorem selected_twoLayer_deficit_two_of_fast_certificate
    {Tlow Tup Llow Lup q N : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hLlow : 1 ≤ Llow)
    (hLup : 1 ≤ Lup)
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hCert :
      FastTwoLayerDeficitTwoCertificate
        (Erdos536.FiberRegionList 1 Tlow)
        (Erdos536.FiberRegionList 1 Tup)
        Llow Lup = true)
    (hAxisLow :
      ((Erdos536.FiberRegionList 1 Tlow).filter
        Erdos536.GridPoint.axisBool).length = Llow)
    (hAxisUp :
      ((Erdos536.FiberRegionList 1 Tup).filter
        Erdos536.GridPoint.axisBool).length = Lup)
    (hLowerSelected :
      Erdos536.FiberSelectedComplete Lower A q)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete Upper A (5 * q))
    (hLowerSub :
      Lower.Subset
        (Erdos536.FiberRegionList 1 Tlow))
    (hUpperSub :
      Upper.Subset
        (Erdos536.FiberRegionList 1 Tup)) :
    Lower.length + Upper.length + 2 ≤ Llow + Lup := by
  have hLowerGamma : Erdos536.GammaFree Lower :=
    Erdos536.fiberSelected_gammaFree
      hq hA hLowerSelected
  have h5q : 0 < 5 * q :=
    Nat.mul_pos (by decide : 0 < (5 : Nat)) hq
  have hUpperGamma : Erdos536.GammaFree Upper :=
    Erdos536.fiberSelected_gammaFree
      h5q hA hUpperSelected
  have hLowerBound : Lower.length ≤ Llow :=
    gammaFree_fiberRegion_length_le_of_axis_count
      hAxisLow hLowerGamma hLowerSub
  have hUpperBound : Upper.length ≤ Lup :=
    gammaFree_fiberRegion_length_le_of_axis_count
      hAxisUp hUpperGamma hUpperSub
  have hFree : TwoLayerTriangleFree Lower Upper :=
    twoLayerTriangleFree_of_selected
      hq hA hLowerSelected hUpperSelected
  exact fast_twoLayer_deficit_two_of_certificate
    hLlow hLup hCert
    hLowerGamma hLowerSub hLowerBound
    hUpperGamma hUpperSub hUpperBound
    hFree

end Erdos536813
