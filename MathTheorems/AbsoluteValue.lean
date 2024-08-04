import Mathlib.Tactic

-- basic theorems
example (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  exact abs_add a b
example (a : ℝ) : |-a| = |a| := by
  exact abs_neg a

lemma abs_pos1 (a : ℝ) : a ≠ 0 → |a| > 0 := by
  intros h₁
  exact abs_pos.mpr h₁

example (a : ℝ) : a < b ↔ b > a := by exact gt_iff_lt

lemma abs_div1 (ε c : ℝ) (h₁ : ε > 0) (h₂ : c > 0) : ε / c > 0 := by
  rw [gt_iff_lt] at *
  exact div_pos h₁ h₂
