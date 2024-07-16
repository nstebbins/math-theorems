import Mathlib.Init.ZeroOne
import Mathlib.Algebra.Group.Defs

namespace Group1

class Group (G : Type) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  left_invertible : ∀ a : G, a * a⁻¹ = 1
  right_invertible : ∀ a : G, a⁻¹ * a = 1
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a

variable (a b c : G)[Group G]

theorem right_cancellation_law : a * c = b * c → a = b := by
  intros h₁
  rw [← Group.mul_one a]
  rw [← Group.left_invertible c]
  rw [← Group.mul_assoc]
  rw [h₁]
  -- go back out from whence you came
  rw [Group.mul_assoc, Group.left_invertible, Group.mul_one]

end Group1
