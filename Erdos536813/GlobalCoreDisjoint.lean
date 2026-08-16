import Erdos536813.GlobalCoreTarget

namespace Erdos536813

/--
The code sets belonging to two distinct 30-coprime cores are disjoint,
because the first coordinate of every code records its core.
-/
theorem coreDepthCodeImage_disjoint
    {N m₁ m₂ : Nat}
    (hne : m₁ ≠ m₂) :
    Disjoint
      ((CoreDepthFinset N m₁).image
        (fun k => (m₁, k)))
      ((CoreDepthFinset N m₂).image
        (fun k => (m₂, k))) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂

  rcases Finset.mem_image.mp hp₁ with
    ⟨k₁, hk₁, hp₁eq⟩
  rcases Finset.mem_image.mp hp₂ with
    ⟨k₂, hk₂, hp₂eq⟩

  have hpair :
      (m₁, k₁) = (m₂, k₂) := by
    calc
      (m₁, k₁) = p := hp₁eq
      _ = (m₂, k₂) := hp₂eq.symm

  exact hne (congrArg Prod.fst hpair)

/--
The family of complete code chains indexed by the global good-core
finset is pairwise disjoint.
-/
theorem goodCore_pairwise_disjoint_codeImages
    {N : Nat} :
    (↑(GoodCoreFinset N) : Set Nat).Pairwise
      (fun m₁ m₂ =>
        Disjoint
          ((CoreDepthFinset N m₁).image
            (fun k => (m₁, k)))
          ((CoreDepthFinset N m₂).image
            (fun k => (m₂, k)))) := by
  intro m₁ hm₁ m₂ hm₂ hne
  exact coreDepthCodeImage_disjoint hne

end Erdos536813
