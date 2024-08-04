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

variable (a b c : ℝ)

example (h₁ : b > 0) : (a / b) < c → a < c * b := by
  intros h₂
  exact (div_lt_iff h₁).mp h₂

example (h₁ : b > 0) : a < (c / b) → a * b < c := by
  intros h₂
  exact (lt_div_iff h₁).mp h₂

lemma rw_not_eq : (¬ a = b) ↔ a ≠ b := by exact Eq.to_iff rfl

lemma rw_not_leq : (¬ a ≥ b) ↔ a < b := by exact not_le

lemma lt_iff_exists_add1 : a < b ↔ ∃ c > 0, a + c = b := by
  constructor
  · intros h₁
    use (b - a)
    constructor
    · exact sub_pos.mpr h₁
    · exact add_sub_cancel a b
  · intros h₁
    rcases h₁ with ⟨c₁, h₂, h₃⟩
    linarith


end Reals
