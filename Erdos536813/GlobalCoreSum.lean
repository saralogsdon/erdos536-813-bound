import Erdos536813.WholeChainTarget

namespace Erdos536813

/--
The set of 30-coprime cores that can occur below `N`.
-/
def GoodCoreFinset (N : Nat) : Finset Nat :=
  (Finset.range (N + 1)).filter GoodThirtyCore

/--
Every admissible five-code base `d ≤ N` has a unique decomposition

    d = m * 5^k

with `m` coprime to 30.

The core `m` is obtained by removing every factor of 5.
-/
def fiveCore (d : Nat) : Nat :=
  d / 5 ^ padicValNat 5 d

/--
The core is 30-coprime whenever the original base is a valid five-code base.
-/
theorem fiveCore_good
    {d : Nat}
    (hd : GoodBaseFive d) :
    GoodThirtyCore (fiveCore d) := by
  exact goodThirtyCore_fiveCore hd

/--
Every valid five-code base has the canonical decomposition into its
30-coprime core and a power of 5.
-/
theorem fiveBase_eq_core_mul_pow
    {d : Nat}
    (hd : GoodBaseFive d) :
    d = fiveCore d * 5 ^ padicValNat 5 d := by
  exact fiveCore_mul_pow_eq_self hd

/--
The core is no larger than the original base.
-/
theorem fiveCore_le
    {d : Nat}
    (hd : GoodBaseFive d) :
    fiveCore d ≤ d := by
  have hpow :
      1 ≤ 5 ^ padicValNat 5 d := by
    positivity
  rw [fiveBase_eq_core_mul_pow hd]
  omega

/--
The canonical core is an admissible global core.
-/
theorem fiveCore_mem_goodCoreFinset
    {N d : Nat}
    (hd : d ≤ N)
    (hGood : GoodBaseFive d) :
    fiveCore d ∈ GoodCoreFinset N := by
  apply Finset.mem_filter.mpr
  constructor
  · have hcore :
      fiveCore d ≤ d :=
      fiveCore_le hGood
    omega
  · exact fiveCore_good hGood

/--
Every global five-code `(m,k)` belongs to exactly one core chain.
-/
theorem globalCode_mem_some_core
    {N m k : Nat}
    (hCode :
      (m,k) ∈ GoodBaseFiveCodeList N) :
    m ∈ GoodCoreFinset N ∧
      k ∈ CoreDepthFinset N m := by
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · have hBase :
        FiveBase m k ≤ N :=
        (mem_goodBaseFiveCodeList_iff.mp hCode).2
      have hmle :
        m ≤ FiveBase m k := by
        unfold FiveBase
        have hpos :
            1 ≤ 5 ^ k := by positivity
        have hm :
            0 < m :=
          (mem_goodBaseFiveCodeList_iff.mp hCode).1.1
        omega
      omega
    · exact (mem_goodBaseFiveCodeList_iff.mp hCode).1
  · exact
      (mem_coreDepthFinset_iff_global_code
        (mem_goodBaseFiveCodeList_iff.mp hCode).1).mpr hCode

/--
Conversely, every depth in a good core chain gives a global five-code.
-/
theorem coreDepth_mem_globalCode
    {N m k : Nat}
    (hm : GoodThirtyCore m)
    (hk : k ∈ CoreDepthFinset N m) :
    (m,k) ∈ GoodBaseFiveCodeList N := by
  exact
    (mem_coreDepthFinset_iff_global_code hm).mp hk

/--
The global code list is exactly the disjoint union of the complete
5-adic chains indexed by good 30-coprime cores.

This is the structural decomposition we will use for the final global sum.
-/
theorem globalCode_eq_biUnion_coreDepth
    {N : Nat} :
    GoodBaseFiveCodeList N =
      GoodCoreFinset N.biUnion
        (fun m =>
          (CoreDepthFinset N m).image
            (fun k => (m,k))) := by
  ext p
  constructor
  · intro hp
    rcases p with ⟨m,k⟩
    have hCore :
        m ∈ GoodCoreFinset N ∧
          k ∈ CoreDepthFinset N m :=
      globalCode_mem_some_core hp
    apply Finset.mem_biUnion.mpr
    refine ⟨m, hCore.1, ?_⟩
    exact Finset.mem_image.mpr
      ⟨k, hCore.2, rfl⟩
  · intro hp
    rcases Finset.mem_biUnion.mp hp with
      ⟨m, hm, hp⟩
    rcases Finset.mem_image.mp hp with
      ⟨k, hk, rfl⟩
    exact coreDepth_mem_globalCode
      ((Finset.mem_filter.mp hm).2)
      hk

/--
The global integer contribution is the sum of the complete core
contributions.
-/
def GlobalIntegerSum
    (A : List Nat)
    (N : Nat) : Nat :=
  ∑ p ∈ GoodBaseFiveCodeList N,
    (Erdos536.FiberIntegerList A
      (FiveBase p.1 p.2)).length

/--
The global baseline is the corresponding sum of the `L23` bounds.
-/
def GlobalBaselineSum
    (N : Nat) : Nat :=
  ∑ p ∈ GoodBaseFiveCodeList N,
    L23 (FiveScale (N / p.1) p.2)

end Erdos536813
