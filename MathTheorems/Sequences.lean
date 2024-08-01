import Mathlib.Tactic

namespace Reals

variable (a : ℕ → ℝ)
variable (l : ℝ)

def Converges : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → |a i - l| < ε

#print Converges

def Cauchy : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ i j : ℕ, i ≥ N ∧ j ≥ N → |a i - a j| < ε

example (a b : ℝ) : |a + b| ≤ |a| + |b| := by exact abs_add a b
example (a : ℝ) : |-a| = |a| := by exact abs_neg a
lemma real_trans (a b: ℝ) : ∀ c : ℝ, a - b = (a + c) - (c - b) := by sorry
#print real_trans

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
  rw [← abs_neg (a j - l)] at r₁
  simp at r₁
  rw [real_trans (a i) (a j) l]
  -- todo: use triangle inequality
  sorry

variable (l₂ : ℝ)

lemma propose_c (a b : ℝ) : a ≠ b → ∃ c : ℝ, c ≠ 0 ∧ a = (b + c) := by
  intros h₁
  use (a - b)
  constructor
  . by_contra h₂
    apply h₁
    rw [← add_zero b]
    rw [← h₂]
    norm_num
  . norm_num

lemma ab_pos (a : ℝ) : a ≠ 0 → |a| > 0 := by
  intros h₁
  exact abs_pos.mpr h₁

#print ab_pos

example : Converges a l ∧ Converges a l₂ → l = l₂ := by
  intros h₁
  repeat rw [Converges] at h₁
  cases' h₁ with h₁ h₂
  by_contra h₃
  apply propose_c at h₃
  cases' h₃ with c h₃
  cases' h₃ with h₃ h₄
  specialize h₁ |c|
  specialize h₂ |c|
  apply ab_pos c at h₃
  have h₅ := h₂ h₃
  have h₆ := h₁ h₃
  cases' h₅ with N₁ h₅
  cases' h₆ with N₂ h₆
  -- think through remaining approach
  sorry

/-
  Algebraic Limit Theorems
-/

variable (c : ℝ)(h_c : c > 0)

def c_a := fun i => c * a i

lemma sim (a b : ℝ) : a > 0 ∧ b > 0 → (a / b) > 0 := by
  intros h₁
  sorry

example : Converges a l → Converges (c_a a c) (c * l) := by
  intros h₁
  rw [Converges] at *
  intros ε h₂
  specialize h₁ (ε / c)
  have h' : ε / c > 0 := by
    apply sim ε c
    constructor
    repeat assumption
  apply h₁ at h'
  cases' h' with N h'
  use N
  intros N₂ h₃
  specialize h' N₂
  apply h' at h₃
  rw [c_a]
  rw [abs_lt] at * -- todo study this missing piece
  cases' h₃ with l₂ r₂
  constructor
  . rw [← mul_sub]
    sorry -- todo how to proceed
  . rw [← mul_sub]
    sorry -- todo how to proceed

variable (b : ℕ → ℝ)

example (h₁ : Converges a l) (h₂ : Converges b l₂) : Converges (fun i => a i + b i) (l + l₂) := by
  sorry


end Reals
