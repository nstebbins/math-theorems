import Mathlib.Tactic

-- basic theorems
example (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  exact abs_add a b
example (a : ℝ) : |-a| = |a| := by
  exact abs_neg a

lemma abs_pos1 (a : ℝ) : a ≠ 0 → |a| > 0 := by
  intros h₁
  exact abs_pos.mpr h₁
