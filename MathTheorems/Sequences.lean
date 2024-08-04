import Mathlib.Tactic
import MathTheorems.AbsoluteValue
import MathTheorems.Reals

namespace Reals

variable (a : ℕ → ℝ)
variable (l : ℝ)

def Converges : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → |a i - l| < ε

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

#print AbsoluteValue.abs_pos1

example : Converges a l ∧ Converges a l₂ → l = l₂ := by
  intros h₁
  repeat rw [Converges] at h₁
  cases' h₁ with h₁ h₂
  by_contra h₃
  apply propose_c at h₃
  rcases h₃ with ⟨c, h₃, h₄⟩
  specialize h₁ |c|
  specialize h₂ |c|
  apply abs_pos c at h₃
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
  cases' h₁ with l r
  rw [gt_iff_lt]
  rw [lt_div_iff]
  rw [zero_mul]
  repeat assumption

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
  rw [abs_lt] at *
  cases' h₃ with l₂ r₂
  constructor
  . rw [← mul_sub]
    sorry -- todo how to proceed
  . rw [← mul_sub]
    sorry -- todo how to proceed

variable (b : ℕ → ℝ)

example (h₁ : Converges a l) (h₂ : Converges b l₂) : Converges (fun i => a i + b i) (l + l₂) := by
  rw [Converges] at *
  intros ε h₃
  obtain ⟨N, hN⟩ := h₁ (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := h₂ (ε / 2) (by linarith)
  let N_max := max N N₂
  use N_max
  intros i h₄
  specialize hN i
  specialize hN₂ i
  have h₅ : N_max ≥ N := by
    apply Nat.le_max_left
  have h₆ : N_max ≥ N₂ := by
    apply Nat.le_max_right
  have h₅ : i ≥ N := by linarith
  have h₆ : i ≥ N₂ := by linarith
  apply hN at h₅
  apply hN₂ at h₆
  rw [abs_lt] at *
  constructor <;> linarith

variable (k : ℝ)

example (h₁ : Converges a l) : Converges (λ i => k + a i) (k + l) := by
  rw [Converges] at *
  intros ε h₂
  obtain ⟨N, h₃⟩ := h₁ ε (by assumption)
  use N
  intros i h₄
  specialize h₃ i
  apply h₃ at h₄
  rw [abs_lt] at *
  constructor <;> linarith


end Reals
