import Mathlib.Tactic

namespace Reals

example (a : ℝ) (b : ℝ) : a < b ↔ ∃ ε, ε > 0 ∧ b = a + ε := by
  constructor
  · intros h₁
    use (b - a)
    constructor
    · exact sub_pos.mpr h₁
      -- src: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Basic.html#add_sub_cancel
    · exact Eq.symm (add_sub_cancel a b)
  · intros h₁
    cases' h₁ with ε h₁
    linarith

-- src: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Basic.html#sub_add_sub_cancel
lemma real_trans (a b: ℝ) : ∀ c : ℝ, a - b = (a - c) + (c - b) := by
  intros c
  exact Eq.symm (sub_add_sub_cancel a c b)

#print real_trans


end Reals
