import Mathlib.Tactic
import Mathlib.Order.RelClasses

namespace PartialOrder1

variable {α : Type}[PartialOrder α]
variable (A P Q: Set α)

def InitialSegment (a : α) : Set α := {x : α | x ∈ A ∧ x < a}
#print InitialSegment

def IsInitialSegment (P : Set α) : Prop := ∃ x ∈ A, P = InitialSegment A x
#print IsInitialSegment

/-
  A Book of Set Theory
  Theorem 4.6
-/

example (h₁ : IsInitialSegment A P) (h₂ : IsInitialSegment P Q) : IsInitialSegment A Q := by
  rw [IsInitialSegment] at *
  cases' h₁ with x₁ h₁
  cases' h₁ with l₃ h₁
  cases' h₂ with x₂ h₂
  cases' h₂ with l₄ h₂
  use x₂
  constructor
  . rw [InitialSegment] at *
    rw [h₁] at l₄
    cases' l₄
    assumption
  . rw [InitialSegment] at *
    ext q₁
    constructor
    . intros h₃
      rw [Set.mem_def, Set.setOf_app_iff] -- dive into ∈
      constructor
      . rw [h₂] at h₃
        rw [Set.mem_def, Set.setOf_app_iff] at h₃
        cases' h₃ with l₁ r₁
        rw [h₁] at l₁
        rw [Set.mem_def, Set.setOf_app_iff] at l₁
        cases' l₁
        assumption
      . rw [h₂] at h₃
        rw [Set.mem_def, Set.setOf_app_iff] at h₃
        cases' h₃ with l₁ r₁
        assumption
    . intros h₃
      rw [h₂]
      rw [Set.mem_def, Set.setOf_app_iff]
      constructor
      . rw [h₁]
        constructor
        . cases' h₃ with l r
          assumption
        . rw [h₁] at l₄
          cases' l₄ with l r
          cases' h₃ with l₂ r₂
          trans x₂
          repeat assumption
      . cases' h₃ with l r
        assumption

end PartialOrder1

namespace PartialOrder1b

variable {α : Type}
variable {A B : Set α}

/-
  A Book of Set Theory
  Remark 4.9
-/

-- subset is a partial order
#print subset_trans

instance : PartialOrder (Set α) where
  le := fun A B => A ⊆ B
  le_refl := by sorry
  le_trans := by
    intros a b c
    exact subset_trans
  le_antisymm := by
    intros a b
    exact subset_antisymm

namespace PartialOrder2

variable {A B C : Type}[PartialOrder A][PartialOrder B][PartialOrder C]
variable (f: A → B)(g: B → C)

def Iso: Prop := f.Bijective ∧ (∀ x y : A, x ≤ y ↔ f x ≤ f y)
#print Iso

/-
  Theorem 4.12
-/

example : Iso f → (∀ x y : A, x < y ↔ f x < f y) := by
  intros h₁ x y
  rw [Iso, Function.Bijective] at *
  cases' h₁ with h₁ h₂
  specialize h₂ x y
  cases' h₂ with l₁ r₁
  constructor
  . intros h₂
    rw [lt_iff_le_and_ne] at *
    cases' h₂ with h₂ h₃
    constructor
    . apply l₁
      assumption
    . -- use injectivity
      cases' h₁ with l₂ r₂
      rw [Function.Injective] at *
      specialize @l₂ x y
      by_contra h₄
      apply h₃
      apply l₂
      assumption
  . intros h₂
    rw [lt_iff_le_and_ne] at *
    cases' h₂ with l₂ r₂
    constructor
    . apply r₁
      assumption
    . by_contra h₂
      apply r₂
      rw [h₂]

/-
  Theorem 4.14(i)
-/

open Function

example : Iso (id : A → A) := by
  rw [Iso, Bijective, Injective, Surjective]
  constructor
  . constructor
    . intros _ _ h
      assumption
    . intros x
      use x
      rfl
  . intros x y
    rfl

/-
  Theorem 4.14(ii)
-/

#print Function.invFun

variable [h : Nonempty A]

variable (b : B)

-- you're allowed to use rw but then you have to prove the assumption right after
lemma f_inv_eq_f (h : f.Surjective) : f (invFun f b) = b := by
  rw [Surjective] at h
  specialize h b
  exact Function.invFun_eq h


#print f_inv_eq_f
#print Function.invFun_eq

example : Iso f → Iso (Function.invFun f) := by
  intros h₁
  rw [Iso] at *
  cases' h₁ with h₁ h₂
  constructor
  . rw [Bijective] at *
    cases' h₁ with h₃ h₄
    constructor
    . sorry
    . rw [Surjective] at *
      intros a₁
      use (f a₁)
      sorry
  . intros b₁ b₂
    constructor
    . intros h₃
      specialize h₂ (f.invFun b₁) (f.invFun b₂)
      rw [h₂]
      rw [Bijective] at h₁
      cases' h₁ with l₁ r₁
      repeat rw [f_inv_eq_f f]
      repeat assumption
    . intros h₃
      specialize h₂ (invFun f b₁) (invFun f b₂)
      sorry

/-
  Theorem 4.14(iii)
-/

example : Iso f ∧ Iso g → Iso (g ∘ f) := by
  repeat rw [Iso]
  intros h₁
  cases' h₁ with l₁ r₁
  cases' l₁ with l₁ l₂
  cases' r₁ with r₁ r₂
  constructor
  . sorry -- already proven in Function.lean
  . intros a₁ a₂
    specialize l₂ a₁ a₂
    rw [l₂] -- leveraging ↔ rewritability to skip steps
    specialize r₂ (f a₁) (f a₂)
    assumption

end PartialOrder2

namespace PartialOrder3

variable (α : Type)[PartialOrder α]
variable (A B C: Set α)

structure Chain where
  S : Set α
  A : Set α
  sub : S ⊆ A
  le_total : ∀ a₁ a₂, (a₁ ∈ S ∧ a₂ ∈ S) → a₁ ≤ a₂ ∨ a₂ ≤ a₁

#print Chain

-- a subset of a chain is a chain
def SubChain (c₁ : Chain α) (h : C ⊆ c₁.S) : Chain α where
  S := C
  A := c₁.S
  sub := by assumption
  le_total := by
    intros a₁ a₂ h₃
    cases' h₃ with h₂ h₃
    rw [Set.subset_def] at h
    apply h at h₂
    apply h at h₃
    apply c₁.le_total
    constructor
    repeat assumption

end PartialOrder3
