import Mathlib.Tactic

namespace Reals

variable (a : ℕ → ℝ)
variable (l : ℝ)

def Converges : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → |a i - l| < ε

#print Converges

def Cauchy : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ i j : ℕ, i ≥ N ∧ j ≥ N → |a i - a j| < ε

example : Converges a l → Cauchy a := by
  intros h₁
  rw [Converges, Cauchy] at *
  intros ε h₂
  specialize h₁ (0.5 * ε)
  have h₃ : 0.5 * ε > 0 := by sorry
  apply h₁ at h₃
  cases' h₃ with N h₃
  use N
  intros i j h
  cases' h with l₁ r₁
  apply h₃ at l₁
  apply h₃ at r₁
  -- TODO flip  a j - l => l - a j
  -- TODO & then use triangle inequality
  sorry


end Reals
