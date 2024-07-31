import Mathlib.Tactic

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
