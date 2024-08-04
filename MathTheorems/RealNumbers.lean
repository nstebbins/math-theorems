import Mathlib.Tactic

namespace Reals

example (a : ℝ) (b : ℝ) : a < b ↔ ∃ ε, ε > 0 ∧ b = a + ε := by
  constructor
  · sorry
  · sorry

lemma real_trans (a b: ℝ) : ∀ c : ℝ, a - b = (a + c) - (c - b) := by
  sorry

#print real_trans


end Reals
