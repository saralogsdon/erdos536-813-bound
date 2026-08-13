import Mathlib

namespace Erdos536

/-- `A` contains no three pairwise distinct elements with the same pairwise LCM. -/
def NoLCMTriangle (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A →
    a ≠ b → a ≠ c → b ≠ c →
    ¬ (Nat.lcm a b = Nat.lcm a c ∧ Nat.lcm a c = Nat.lcm b c)

/-- `A` is supported on `{1, ..., N}`. -/
def SupportedUpTo (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n ∈ A, 1 ≤ n ∧ n ≤ N

/-- Admissible sets for Erdős Problem #536. -/
def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  SupportedUpTo N A ∧ NoLCMTriangle A

/-- The extremal function from Erdős Problem #536. -/
def f (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).powerset.filter fun A => Admissible N A).sup Finset.card

end Erdos536
