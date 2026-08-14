import Erdos536813.FastTwoLayerCore

namespace Erdos536813

/-!
## Cardinality-restricted fast two-layer certificates

For a deficit-two counterexample with one-layer bounds
`|Lower| ≤ Llow` and `|Upper| ≤ Lup`, contradiction implies
`Llow - 1 ≤ |Lower|` and `Lup - 1 ≤ |Upper|`.

Hence each candidate family only needs the two possible sizes
`L - 1` and `L`, rather than all `2^|D|` sublists of the board.
-/

/-- Gamma-free sublists of exactly the two near-extremal sizes `L-1` and `L`. -/
def NearExtremalGammaFreeFamiliesByLength
    (D : List Erdos536.GridPoint)
    (L : Nat) : List (List Erdos536.GridPoint) :=
  (D.sublistsLen (L - 1) ++ D.sublistsLen L).filter
    GammaFreeFiniteBool

/-- Fast certificate using only the two cardinalities that can violate deficit two. -/
def CardinalityFastTwoLayerDeficitTwoCertificate
    (Dlow Dup : List Erdos536.GridPoint)
    (Llow Lup : Nat) : Bool :=
  let lowerFamilies :=
    NearExtremalGammaFreeFamiliesByLength Dlow Llow
  let upperFamilies :=
    NearExtremalGammaFreeFamiliesByLength Dup Lup
  let witnesses :=
    CrossWitnesses Dlow Dup
  lowerFamilies.all (fun Lower =>
    upperFamilies.all (fun Upper =>
      FastTwoLayerPairDeficitCheck
        witnesses Llow Lup Lower Upper))

/-- Soundness of the cardinality-restricted fast certificate. -/
theorem cardinality_fast_twoLayer_deficit_two_of_certificate
    {Dlow Dup Lower Upper : List Erdos536.GridPoint}
    {Llow Lup : Nat}
    (hLlow : 1 ≤ Llow)
    (hLup : 1 ≤ Lup)
    (hCert :
      CardinalityFastTwoLayerDeficitTwoCertificate
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
  have hLowerGamma' : Erdos536.GammaFree Lower' :=
    gammaFree_of_perm hLowerPerm hLowerGamma
  have hLowerGammaBool :
      GammaFreeFiniteBool Lower' = true :=
    gammaFreeFiniteBool_of_gammaFree hLowerGamma'
  have hLowerLenEq : Lower'.length = Lower.length :=
    hLowerPerm.length_eq
  have hLowerNear' : Llow - 1 ≤ Lower'.length := by
    omega
  have hLowerBound' : Lower'.length ≤ Llow := by
    omega
  have hLowerLenCases :
      Lower'.length = Llow - 1 ∨ Lower'.length = Llow := by
    omega
  have hLowerSized :
      Lower' ∈
        Dlow.sublistsLen (Llow - 1) ++ Dlow.sublistsLen Llow := by
    apply List.mem_append.mpr
    rcases hLowerLenCases with hLen | hLen
    · exact Or.inl ((List.mem_sublistsLen).2 ⟨hLowerSublist, hLen⟩)
    · exact Or.inr ((List.mem_sublistsLen).2 ⟨hLowerSublist, hLen⟩)
  have hLowerCand :
      Lower' ∈ NearExtremalGammaFreeFamiliesByLength Dlow Llow := by
    apply List.mem_filter.mpr
    constructor
    · exact hLowerSized
    · simpa [hLowerGammaBool]

  have hUpperSubperm : List.Subperm Upper Dup :=
    hUpperGamma.1.subperm hUpperSub
  rcases hUpperSubperm with
    ⟨Upper', hUpperPerm, hUpperSublist⟩
  have hUpperGamma' : Erdos536.GammaFree Upper' :=
    gammaFree_of_perm hUpperPerm hUpperGamma
  have hUpperGammaBool :
      GammaFreeFiniteBool Upper' = true :=
    gammaFreeFiniteBool_of_gammaFree hUpperGamma'
  have hUpperLenEq : Upper'.length = Upper.length :=
    hUpperPerm.length_eq
  have hUpperNear' : Lup - 1 ≤ Upper'.length := by
    omega
  have hUpperBound' : Upper'.length ≤ Lup := by
    omega
  have hUpperLenCases :
      Upper'.length = Lup - 1 ∨ Upper'.length = Lup := by
    omega
  have hUpperSized :
      Upper' ∈
        Dup.sublistsLen (Lup - 1) ++ Dup.sublistsLen Lup := by
    apply List.mem_append.mpr
    rcases hUpperLenCases with hLen | hLen
    · exact Or.inl ((List.mem_sublistsLen).2 ⟨hUpperSublist, hLen⟩)
    · exact Or.inr ((List.mem_sublistsLen).2 ⟨hUpperSublist, hLen⟩)
  have hUpperCand :
      Upper' ∈ NearExtremalGammaFreeFamiliesByLength Dup Lup := by
    apply List.mem_filter.mpr
    constructor
    · exact hUpperSized
    · simpa [hUpperGammaBool]

  have hAll :
      ∀ L ∈ NearExtremalGammaFreeFamiliesByLength Dlow Llow,
        ∀ U ∈ NearExtremalGammaFreeFamiliesByLength Dup Lup,
          FastTwoLayerPairDeficitCheck
            (CrossWitnesses Dlow Dup)
            Llow Lup L U = true := by
    simpa [CardinalityFastTwoLayerDeficitTwoCertificate] using hCert

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

/-- Selected-fiber consequence of the cardinality-restricted certificate. -/
theorem selected_twoLayer_deficit_two_of_cardinality_fast_certificate
    {Tlow Tup Llow Lup q N : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hLlow : 1 ≤ Llow)
    (hLup : 1 ≤ Lup)
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hCert :
      CardinalityFastTwoLayerDeficitTwoCertificate
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
  exact cardinality_fast_twoLayer_deficit_two_of_certificate
    hLlow hLup hCert
    hLowerGamma hLowerSub hLowerBound
    hUpperGamma hUpperSub hUpperBound
    hFree

end Erdos536813
