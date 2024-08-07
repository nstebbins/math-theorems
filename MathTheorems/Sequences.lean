import Mathlib.Tactic
import MathTheorems.AbsoluteValue
import MathTheorems.RealNumbers

namespace Reals

variable (a : ℕ → ℝ)
variable (l : ℝ)

def Converges : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → |a i - l| < ε

def Cauchy : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ i j : ℕ, i ≥ N ∧ j ≥ N → |a i - a j| < ε

/-
  Convergence => Cauchy
-/

example : Converges a l → Cauchy a := by
  intros h₁
  rw [Converges, Cauchy] at *
  intros ε h₂
  specialize h₁ (0.5 * ε)
  have h₃ : 0.5 * ε > 0 := by exact Real.mul_pos (by norm_num) h₂
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
  rw [abs_lt] at *
  cases' r₁ with l₂ r₂
  cases' l₁ with l₁ r₁
  have h₄ : 0.5 * ε + 0.5 * ε = ε := by
        rw [← mul_add]
        ring
  constructor
  · rw [← h₄]
    rw [neg_add]
    apply add_lt_add l₁ l₂
  · rw [← h₄]
    apply add_lt_add r₁ r₂

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

#print abs_pos1

/-
  Uniqueness of Limits
-/

#print lt_iff_exists_add

example : Converges a l ∧ Converges a l₂ → l = l₂ := by
  intros h₁
  repeat rw [Converges] at h₁
  rcases h₁ with ⟨h₁, h₂⟩
  by_contra h₃
  rw [rw_not_eq] at h₃
  rw [ne_iff_lt_or_gt] at h₃
  cases' h₃ with h₃ h₃
  · let ε := 0.5 * (l₂ - l)
    specialize h₁ ε
    specialize h₂ ε
    have h₄ : ε > 0 := by
      apply Real.mul_pos
      · norm_num
      · linarith
    have h₅ := h₁ h₄
    have h₆ := h₂ h₄
    rcases h₅ with ⟨N₁, h₅⟩
    rcases h₆ with ⟨N₂, h₆⟩
    let N := max N₁ N₂
    specialize h₅ N (by exact Nat.le_max_left N₁ N₂)
    specialize h₆ N (by exact Nat.le_max_right N₁ N₂)
    have h₇ : |a N - l + (a N - l₂)| ≤ |a N - l| + |a N - l₂| := by
      exact abs_add (a N - l) (a N - l₂)
    rw [abs_lt] at *
    rw [abs_le] at *
    have : 2 * ε = l₂ - l := by ring
    linarith -- note: just had to get rid of multiplication!
  · sorry

/-
  Algebraic Limit Theorems
-/

variable (c : ℝ)
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

lemma sim (a b : ℝ) : a > 0 ∧ b > 0 → (a / b) > 0 := by
  intros h₁
  cases' h₁ with l r
  rw [gt_iff_lt]
  rw [lt_div_iff]
  rw [zero_mul]
  repeat assumption

example (h : c > 0) : Converges a l → Converges (fun i => c * a i) (c * l) := by
  intros h₁
  rw [Converges] at *
  intros ε h₂
  obtain ⟨N, h₁⟩ := h₁ (ε / c) (by exact abs_div1 ε c h₂ h)
  use N
  intros i h₃
  specialize h₁ i
  apply h₁ at h₃
  rw [abs_lt] at *
  cases' h₃ with h₄ h₅
  constructor
  · rw [← neg_div] at h₄
    rw [div_lt_iff] at h₄
    rw [sub_mul] at h₄
    linarith
    assumption
  · rw [lt_div_iff] at h₅
    rw [sub_mul] at h₅
    rw [mul_comm] at h₅
    nth_rewrite 2 [mul_comm] at h₅
    repeat assumption

/-
  Order Limit Theorem
-/

example : (∀ i : ℕ, a i ≥ 0) ∧ Converges a l → l ≥ 0 := by
  intros h₁
  rcases h₁ with ⟨h₁, h₂⟩
  rw [Converges] at h₂
  by_contra h₃
  rw [not_le] at h₃
  rw [lt_iff_exists_add1] at h₃
  rcases h₃ with ⟨c₁, h₃, h₄⟩
  specialize h₂ c₁ (by assumption)
  cases' h₂ with N h₅
  specialize h₅ N (by rfl)
  specialize h₁ N
  rw [abs_lt] at h₅
  cases' h₅ with h₅ h₆
  linarith

end Reals
