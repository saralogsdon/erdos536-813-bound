import Erdos536813.AdjacentLayer

namespace Erdos536813

/-!
## Exact two-layer finite certificates

For the remaining small scales, the large-annulus argument is not strong
enough.  We therefore certify the two-layer statement directly.

The executable certificate does **not** enumerate every pair of subsets.
For each layer it first keeps only Gamma-free subfamilies with one-layer
deficit at most one.  If a two-layer family had total deficit at most one,
its two slices would necessarily occur in these near-extremal lists.
The certificate then checks that every such pair either already has total
deficit at least two or contains an LCM triangle across the two layers.
-/

/-- The unscaled natural-number values represented by two adjacent 5-adic layers. -/
def TwoLayerValues
    (Lower Upper : List Erdos536.GridPoint) : List Nat :=
  Lower.map (fun p => Erdos536.fiberValue 1 p) ++
    Upper.map (fun p => 5 * Erdos536.fiberValue 1 p)

/-- Mathematical two-layer triangle-freeness, phrased on the unscaled values. -/
def TwoLayerTriangleFree
    (Lower Upper : List Erdos536.GridPoint) : Prop :=
  ∀ a ∈ TwoLayerValues Lower Upper,
    ∀ b ∈ TwoLayerValues Lower Upper,
      ∀ c ∈ TwoLayerValues Lower Upper,
        ¬ Erdos536.IsLcmTriangle a b c

/-- Executable Boolean form of `IsLcmTriangle`. -/
def IsLcmTriangleBool (a b c : Nat) : Bool :=
  decide (a ≠ b) &&
    decide (a ≠ c) &&
    decide (b ≠ c) &&
    decide (Nat.lcm a b = Nat.lcm a c) &&
    decide (Nat.lcm a c = Nat.lcm b c)

theorem isLcmTriangleBool_eq_true_iff
    (a b c : Nat) :
    IsLcmTriangleBool a b c = true ↔
      Erdos536.IsLcmTriangle a b c := by
  simp [IsLcmTriangleBool, Erdos536.IsLcmTriangle, and_assoc]

/-- Executable two-layer triangle-freeness checker. -/
def TwoLayerTriangleFreeBool
    (Lower Upper : List Erdos536.GridPoint) : Bool :=
  let V := TwoLayerValues Lower Upper
  V.all (fun a =>
    V.all (fun b =>
      V.all (fun c =>
        ! IsLcmTriangleBool a b c)))

theorem isLcmTriangleBool_eq_false_iff
    (a b c : Nat) :
    IsLcmTriangleBool a b c = false ↔
      ¬ Erdos536.IsLcmTriangle a b c := by
  constructor
  · intro hFalse hTri
    have hTrue : IsLcmTriangleBool a b c = true :=
      (isLcmTriangleBool_eq_true_iff a b c).2 hTri
    have hContra : False := by
      simpa [hTrue] using hFalse
    exact hContra.elim
  · intro hNot
    cases hBool : IsLcmTriangleBool a b c with
    | false =>
        rfl
    | true =>
        exfalso
        apply hNot
        exact (isLcmTriangleBool_eq_true_iff a b c).1 hBool

theorem twoLayerTriangleFreeBool_eq_true_iff
    (Lower Upper : List Erdos536.GridPoint) :
    TwoLayerTriangleFreeBool Lower Upper = true ↔
      TwoLayerTriangleFree Lower Upper := by
  simp [TwoLayerTriangleFreeBool, TwoLayerTriangleFree,
    isLcmTriangleBool_eq_false_iff]

/-- Triangle-freeness depends only on the underlying multisets of values. -/
theorem triangleFreeValues_of_perm
    {V W : List Nat}
    (hPerm : V.Perm W)
    (hFree :
      ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W,
        ¬ Erdos536.IsLcmTriangle a b c) :
    ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V,
      ¬ Erdos536.IsLcmTriangle a b c := by
  intro a ha b hb c hc
  exact hFree
    a ((hPerm.mem_iff).1 ha)
    b ((hPerm.mem_iff).1 hb)
    c ((hPerm.mem_iff).1 hc)

/-- Permuting either slice preserves two-layer triangle-freeness. -/
theorem twoLayerTriangleFree_of_perm
    {Lower Lower' Upper Upper' : List Erdos536.GridPoint}
    (hLower : Lower'.Perm Lower)
    (hUpper : Upper'.Perm Upper)
    (hFree : TwoLayerTriangleFree Lower Upper) :
    TwoLayerTriangleFree Lower' Upper' := by
  have hLowerVals :
      (Lower'.map (fun p => Erdos536.fiberValue 1 p)).Perm
        (Lower.map (fun p => Erdos536.fiberValue 1 p)) :=
    hLower.map _
  have hUpperVals :
      (Upper'.map (fun p => 5 * Erdos536.fiberValue 1 p)).Perm
        (Upper.map (fun p => 5 * Erdos536.fiberValue 1 p)) :=
    hUpper.map _
  have hVals :
      (TwoLayerValues Lower' Upper').Perm
        (TwoLayerValues Lower Upper) := by
    simpa [TwoLayerValues] using hLowerVals.append hUpperVals
  exact triangleFreeValues_of_perm hVals hFree

/--
Every unscaled value represented by a selected lower/upper pair becomes an
actual member of `A` after multiplication by the common scale `q`.
-/
theorem scaled_twoLayerValue_mem
    {q : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hLowerSelected :
      Erdos536.FiberSelectedComplete Lower A q)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete Upper A (5 * q))
    {a : Nat}
    (ha : a ∈ TwoLayerValues Lower Upper) :
    q * a ∈ A := by
  rw [TwoLayerValues] at ha
  rcases List.mem_append.mp ha with haLower | haUpper
  · rcases List.mem_map.mp haLower with ⟨p, hp, rfl⟩
    have hpA : Erdos536.fiberValue q p ∈ A :=
      (hLowerSelected.2 p).1 hp
    simpa [Erdos536.fiberValue, Nat.mul_assoc] using hpA
  · rcases List.mem_map.mp haUpper with ⟨p, hp, rfl⟩
    have hpA : Erdos536.fiberValue (5 * q) p ∈ A :=
      (hUpperSelected.2 p).1 hp
    simpa [Erdos536.fiberValue, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using hpA

/--
An actual LCM-triangle-free set induces a triangle-free pair of adjacent
unscaled 5-adic slices.
-/
theorem twoLayerTriangleFree_of_selected
    {q N : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hLowerSelected :
      Erdos536.FiberSelectedComplete Lower A q)
    (hUpperSelected :
      Erdos536.FiberSelectedComplete Upper A (5 * q)) :
    TwoLayerTriangleFree Lower Upper := by
  intro a ha b hb c hc hTri
  have haA : q * a ∈ A :=
    scaled_twoLayerValue_mem hLowerSelected hUpperSelected ha
  have hbA : q * b ∈ A :=
    scaled_twoLayerValue_mem hLowerSelected hUpperSelected hb
  have hcA : q * c ∈ A :=
    scaled_twoLayerValue_mem hLowerSelected hUpperSelected hc
  have hScaled :
      Erdos536.IsLcmTriangle (q * a) (q * b) (q * c) :=
    scale_is_lcmTriangle hq hTri
  exact hA.2.2
    (q * a) haA
    (q * b) hbA
    (q * c) hcA
    hScaled

/--
Near-extremal Gamma-free families: all sublists of `D` that are Gamma-free
and have length at least `B`.
-/
def NearExtremalGammaFreeFamilies
    (D : List Erdos536.GridPoint)
    (B : Nat) : List (List Erdos536.GridPoint) :=
  D.sublists.filter (fun U =>
    GammaFreeFiniteBool U && decide (B ≤ U.length))

/--
For one pair of near-extremal slices, either the desired two-unit deficit
already holds or the pair must fail the two-layer triangle-free test.
-/
def TwoLayerPairDeficitCheck
    (Llow Lup : Nat)
    (Lower Upper : List Erdos536.GridPoint) : Bool :=
  if Lower.length + Upper.length + 2 ≤ Llow + Lup then
    true
  else
    ! TwoLayerTriangleFreeBool Lower Upper

/-- Executable finite certificate for a two-layer deficit of at least two. -/
def TwoLayerDeficitTwoCertificate
    (Dlow Dup : List Erdos536.GridPoint)
    (Llow Lup : Nat) : Bool :=
  (NearExtremalGammaFreeFamilies Dlow (Llow - 1)).all
    (fun Lower =>
      (NearExtremalGammaFreeFamilies Dup (Lup - 1)).all
        (fun Upper =>
          TwoLayerPairDeficitCheck Llow Lup Lower Upper))

/--
Soundness of the finite two-layer certificate.

The only mathematical inputs besides the certificate are the ordinary
one-layer bounds `|Lower| ≤ Llow` and `|Upper| ≤ Lup`.
-/
theorem twoLayer_deficit_two_of_certificate
    {Dlow Dup Lower Upper : List Erdos536.GridPoint}
    {Llow Lup : Nat}
    (hLlow : 1 ≤ Llow)
    (hLup : 1 ≤ Lup)
    (hCert :
      TwoLayerDeficitTwoCertificate Dlow Dup Llow Lup = true)
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
  rcases hLowerSubperm with ⟨Lower', hLowerPerm, hLowerSublist⟩
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
      Lower' ∈ NearExtremalGammaFreeFamilies Dlow (Llow - 1) := by
    apply List.mem_filter.mpr
    constructor
    · exact hLowerMem
    · simp [hLowerGammaBool, hLowerNear']

  have hUpperSubperm : List.Subperm Upper Dup :=
    hUpperGamma.1.subperm hUpperSub
  rcases hUpperSubperm with ⟨Upper', hUpperPerm, hUpperSublist⟩
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
      Upper' ∈ NearExtremalGammaFreeFamilies Dup (Lup - 1) := by
    apply List.mem_filter.mpr
    constructor
    · exact hUpperMem
    · simp [hUpperGammaBool, hUpperNear']

  have hAll :
      ∀ L ∈ NearExtremalGammaFreeFamilies Dlow (Llow - 1),
        ∀ U ∈ NearExtremalGammaFreeFamilies Dup (Lup - 1),
          TwoLayerPairDeficitCheck Llow Lup L U = true := by
    simpa [TwoLayerDeficitTwoCertificate] using hCert

  have hPair :=
    hAll Lower' hLowerCand Upper' hUpperCand

  have hTooBig' :
      ¬ (Lower'.length + Upper'.length + 2 ≤ Llow + Lup) := by
    omega

  have hNotFreeBool :
      ! TwoLayerTriangleFreeBool Lower' Upper' = true := by
    simpa [TwoLayerPairDeficitCheck, hTooBig'] using hPair

  have hFree' : TwoLayerTriangleFree Lower' Upper' :=
    twoLayerTriangleFree_of_perm hLowerPerm hUpperPerm hFree
  have hFreeBool :
      TwoLayerTriangleFreeBool Lower' Upper' = true :=
    (twoLayerTriangleFreeBool_eq_true_iff Lower' Upper').2 hFree'

  simp [hFreeBool] at hNotFreeBool

/-!
### Next exact states: `T = 48, 54, 60, 64`

For these states we reuse the general two-layer certificate.  The ordinary
one-layer bounds are obtained structurally from Kenta Kitamura's axis-projection
bound, with only the tiny axis counts evaluated by `native_decide`.
-/

/-- Structural one-layer Gamma-free bound for a concrete fiber region. -/
theorem gammaFree_fiberRegion_length_le_axis
    {T : Nat}
    {S : List Erdos536.GridPoint}
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (Erdos536.FiberRegionList 1 T)) :
    S.length ≤
      ((Erdos536.FiberRegionList 1 T).filter
        Erdos536.GridPoint.axisBool).length := by
  have hComplete :
      Erdos536.FiberRegionComplete
        (Erdos536.FiberRegionList 1 T) 1 T :=
    Erdos536.fiberRegionList_complete
      (m := 1) (N := T) (by decide : 0 < (1 : Nat))
  exact Erdos536.gammaFree_card_le_axis_card
    hSub
    (Erdos536.fiberRegionComplete_downClosed hComplete)
    hGamma

/-- Convenient specialization when the axis count has been certified. -/
theorem gammaFree_fiberRegion_length_le_of_axis_count
    {T B : Nat}
    {S : List Erdos536.GridPoint}
    (hAxis :
      ((Erdos536.FiberRegionList 1 T).filter
        Erdos536.GridPoint.axisBool).length = B)
    (hGamma : Erdos536.GammaFree S)
    (hSub : S.Subset (Erdos536.FiberRegionList 1 T)) :
    S.length ≤ B := by
  have h :=
    gammaFree_fiberRegion_length_le_axis
      (T := T) hGamma hSub
  simpa [hAxis] using h

/--
Generic selected-fiber form of an exact two-layer certificate on two concrete
fiber regions.
-/
theorem selected_twoLayer_deficit_two_of_certificate
    {Tlow Tup Llow Lup q N : Nat}
    {A : List Nat}
    {Lower Upper : List Erdos536.GridPoint}
    (hLlow : 1 ≤ Llow)
    (hLup : 1 ≤ Lup)
    (hq : 0 < q)
    (hA : Erdos536.LcmTriangleFreeUpTo N A)
    (hCert :
      TwoLayerDeficitTwoCertificate
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
      Lower.Subset (Erdos536.FiberRegionList 1 Tlow))
    (hUpperSub :
      Upper.Subset (Erdos536.FiberRegionList 1 Tup)) :
    Lower.length + Upper.length + 2 ≤ Llow + Lup := by
  have hLowerGamma : Erdos536.GammaFree Lower :=
    Erdos536.fiberSelected_gammaFree hq hA hLowerSelected
  have h5q : 0 < 5 * q :=
    Nat.mul_pos (by decide : 0 < (5 : Nat)) hq
  have hUpperGamma : Erdos536.GammaFree Upper :=
    Erdos536.fiberSelected_gammaFree h5q hA hUpperSelected
  have hLowerBound : Lower.length ≤ Llow :=
    gammaFree_fiberRegion_length_le_of_axis_count
      hAxisLow hLowerGamma hLowerSub
  have hUpperBound : Upper.length ≤ Lup :=
    gammaFree_fiberRegion_length_le_of_axis_count
      hAxisUp hUpperGamma hUpperSub
  have hFree : TwoLayerTriangleFree Lower Upper :=
    twoLayerTriangleFree_of_selected
      hq hA hLowerSelected hUpperSelected
  exact twoLayer_deficit_two_of_certificate
    hLlow hLup hCert
    hLowerGamma hLowerSub hLowerBound
    hUpperGamma hUpperSub hUpperBound
    hFree

end Erdos536813
