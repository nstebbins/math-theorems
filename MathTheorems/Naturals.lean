
import Mathlib.Tactic

namespace Naturals

variable (m n k : ℕ)

open Nat

/-
  Theorem 6.11
-/

theorem succ_eq_one_add : n.succ = 1 + n := by
  induction n
  case zero => rw [one_eq_succ_zero]
  case succ n h₁ =>
    repeat rw [one_eq_succ_zero]
    rw [add_succ]
    rw [add_zero]
    rw [← one_eq_succ_zero]
    nth_rewrite 1 [h₁]
    rw [← add_succ]

/-
  Theorem 6.12
-/

theorem zero_add : 0 + n = n := by
  induction n
  case zero => rw [add_zero]
  case succ n h₁ =>
    repeat rw [one_eq_succ_zero]
    repeat rw [add_succ]
    rw [h₁, add_zero]

/-
  Theorem 6.13
-/

theorem add_assoc: (m + n) + k = m + (n + k) := by sorry

/-
  Theorem 6.14 (leveraging custom-defined succ_add)
-/

lemma succ_add : n.succ + m = (n + m).succ := by
  induction' m with m hn
  . repeat rw [add_zero]
  . rw [add_succ]
    rw [hn]
    rw [add_succ]

theorem add_comm: (m + n) = n + m := by
  induction' n with n hn
  . rw [zero_add, add_zero]
  . repeat rw [add_succ]
    rw [hn]
    rw [succ_add]

/-
  Theorem 6.16
-/

theorem zero_mul : 0 * n = 0 := by
  induction' n with n hn
  . rw [mul_zero]
  . rw [mul_succ]
    rw [add_zero]
    assumption

/-
  Theorem 6.17
-/

theorem one_mul : 1 * n = n := by
  induction' n with n hn
  . rw [mul_zero]
  . rw [mul_succ]
    rw [hn]

end Naturals
