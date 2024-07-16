import Mathlib.Init.ZeroOne
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

namespace Group1

class Group (G : Type) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  left_invertible : ∀ a : G, a * a⁻¹ = 1
  right_invertible : ∀ a : G, a⁻¹ * a = 1
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a

variable (a b c : G)[Group G]

/-
  Properties of Groups
-/

theorem right_cancellation_law : a * c = b * c → a = b := by
  intros h₁
  rw [← Group.mul_one a]
  rw [← Group.left_invertible c]
  rw [← Group.mul_assoc]
  rw [h₁]
  -- go back out from whence you came
  rw [Group.mul_assoc, Group.left_invertible, Group.mul_one]

theorem left_cancellation_law : c * a = c * b → a = b := by
  intros h₁
  rw [← Group.one_mul a]
  rw [← Group.right_invertible c]
  rw [Group.mul_assoc]
  rw [h₁]
  -- go back out from whence you came
  rw [← Group.mul_assoc, Group.right_invertible, Group.one_mul]

theorem inverses_of_each_other : a * b = 1 → a = b⁻¹ ∧ b = a⁻¹ := by
  intros h₁
  constructor
  . apply right_cancellation_law a b⁻¹ b
    rw [Group.right_invertible]
    assumption
  . rw [← Group.left_invertible a] at h₁
    apply left_cancellation_law b a⁻¹ a
    assumption

theorem inverse_is_unique : a * b = 1 ∧ a * c = 1 → b = c := by
  intros h₁
  cases' h₁ with l₁ r₁
  apply inverses_of_each_other at l₁
  apply inverses_of_each_other at r₁
  cases' l₁ with h₁ h₂
  cases' r₁ with h₃ h₄
  rw [h₂, h₄]

class AbelianGroup (G: Type) extends Group G where
  mul_comm : ∀ a b : G, a * b = b * a

structure Subgroup (X: Type)[Group X] where
  carrier: Set X  -- subset
  closed_under_mul: ∀ a b : X, a ∈ carrier ∧ b ∈ carrier → a * b ∈ carrier
  closed_under_inv: ∀ a : X, a ∈ carrier → a⁻¹ ∈ carrier
  nonempty: ∃ a : X, a ∈ carrier

variable (s : Subgroup G)

theorem identity_in_subgroup : (1: G) ∈ s.carrier := by
  cases' s.nonempty with a h₁
  rw [← Group.left_invertible a]
  apply s.closed_under_mul a (a⁻¹)
  constructor
  case intro.right =>
    apply s.closed_under_inv a
    assumption
  case intro.left => assumption

end Group1
