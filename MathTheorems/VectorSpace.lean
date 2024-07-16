import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

namespace VectorSpace1

class ScalarMultiplication (V F: Type)[Field F][AddCommGroup V] extends HSMul F V V

class VectorSpace (V F: Type)[Field F][AddCommGroup V] extends ScalarMultiplication V F where
  scalar_mul_assoc : ∀ (a b : F) (v : V), a • (b • v) = (a * b) • v
  scalar_left_distrib : ∀ (u: F) (v w : V), u • (v + w) = (u • v) + (u • w)
  scalar_right_distrib : ∀ (u v: F) (w : V), (u + v) • w = (u • w) + (v • w)
  scalar_one_mul: ∀ (v : V), (1 : F) • v = v

variable {V F: Type}[Field F][AddCommGroup V][V' : VectorSpace V F]
variable (a b : F)(u v w : V)

theorem cancel_left : u + v = u + w → v = w := by
  intro h₁
  sorry

#check cancel_left

theorem zero_mul : (0 : F) • v = (0 : V) := by sorry

theorem mul_zero : a • (0 : V) = 0 := by sorry

theorem neg_one_mul : (-1 : F) • v = -v := by
  apply VectorSpace1.cancel_left v (-1 • v) (-v)
  nth_rewrite 1 [← V'.scalar_one_mul v]
  rw [← V'.scalar_right_distrib]
  simp
  apply VectorSpace1.zero_mul

class SameLength {V F : Type} where
  vecs : List V
  scalars : List F
  same_length : vecs.length = scalars.length

def linear_combination (scalars: List F) (vectors: List V) : V :=
  let vecs := (scalars.zip vectors).map λ (c, v) => c • v
  vecs.foldl (λ v₁ v₂ => v₁ + v₂) (0: V)

def span_ (vectors : List V) : Set V :=
  { v : V | ∃ (scalars : List F), scalars.length = vectors.length ∧
    v = linear_combination scalars vectors
  }

#check span_

def id (a : Type) (b : a) := b -- explicit
def id2 {a : Type} (b : a) := b -- implicit

#eval id Nat 5
#eval id2 5
#eval @id2 Nat 5

-- how to use zip
#eval [1, 2, 3].zip [4, 5, 6]

-- how to use map
#eval [1, 2, 3].map (λ x => x + 1)
#eval ([(1, 2), (3, 4)]).map (λ (a, b) => a + b)

-- sum over elements
#eval [1, 2, 3].foldl (λ x y => x + y) 0

class FiniteDimensionalVectorSpace (V F: Type)[F' : Field F][G : AddCommGroup V] extends VectorSpace V F where
  dim : Nat
  vecs : List V
  is_finite : vecs.length = dim
  coverage : ∀ (v : V), v ∈ @span_ V F F' G _ vecs

end VectorSpace1
