import Mathlib.Tactic

namespace Set1

set_option diagnostics true

variable {X: Type}
variable (A : Set X)

/- how do i define successor from set theory? -/
def Singleton : Set (Set X) := {x | x = A}
def Successor : Set X := {x | x ∈ A ∨ x ∈ Singleton}

end Set1

/-
  A Book of Set Theory
  Chapter 1.2
-/

namespace Set2

variable {X: Type}
variable (A B : Set X)

/-
  Theorem 1.11
-/

example : A = A := by
  ext x₁
  constructor <;> intros h₁
  repeat assumption

example : (A = B) → (B = A) := by
  repeat rw [Set.ext_iff] at *
  intros h₁ a
  specialize h₁ a
  cases' h₁ with l₁ r₁
  constructor <;> intros h₂
  apply r₁ h₂
  apply l₁ h₂

example : (A = B ∧ B = C) → A = C := by
  intros h₁
  cases' h₁ with l₁ r₁
  repeat rw [Set.ext_iff] at *
  intros a₁
  specialize l₁ a₁
  specialize r₁ a₁
  cases' l₁ with l₁ l₂
  cases' r₁ with r₁ r₂
  constructor <;> intros H₁
  apply r₁
  apply l₁
  assumption
  apply l₂
  apply r₂
  assumption

example : (A ⊆ B ∧ B ⊆ A) → A = B := by
  intros h₁
  cases' h₁ with l₁ r₁
  rw [Set.subset_def] at *
  rw [Set.ext_iff]
  intros a
  specialize l₁ a
  specialize r₁ a
  constructor
  exact l₁
  exact r₁

example : (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
  intros h₁
  cases' h₁ with l₁ r₁
  rw [Set.subset_def] at *
  intros a
  specialize l₁ a
  specialize r₁ a
  intros h₁
  apply r₁
  apply l₁
  assumption

/-
  Theorem 1.17
-/

example : ∅ ⊆ A := by
  rw [Set.subset_def]
  intros a h₁
  exfalso
  apply h₁

/-
  Theorem 1.20
-/

example : A ⊆ A ∪ B := by
  rw [Set.subset_def]
  intros a h₁
  rw [Set.union_def]
  rw [Set.mem_def, Set.setOf_app_iff]
  left
  assumption

example : B ⊆ A ∪ B := by
  rw [Set.subset_def]
  intros a h₁
  rw [Set.union_def]
  rw [Set.mem_def, Set.setOf_app_iff]
  right
  assumption

example : A ∩ B ⊆ A := by
  rw [Set.subset_def]
  intros a h₁
  rw [Set.inter_def] at h₁
  rw [Set.mem_def, Set.setOf_app_iff] at h₁
  cases' h₁ with l₁ r₁
  assumption

example : A ∩ B ⊆ B := by
  rw [Set.subset_def]
  intros a h₁
  rw [Set.inter_def] at h₁
  rw [Set.mem_def, Set.setOf_app_iff] at h₁
  cases' h₁ with l₁ r₁
  assumption

/-
  Theorem 1.21
-/

example : A ⊆ B → A ∪ B = B := by sorry

example : A ∪ B = B → A ⊆ B := by
  intros h₁
  rw [Set.subset_def]
  intros a h₂
  rw [Set.ext_iff] at *
  specialize h₁ a
  cases' h₁ with l₁ r₁
  apply l₁
  left
  assumption

example : A ⊆ B → A ∩ B = A := by sorry

example : A ∩ B = A → A ⊆ B := by
  intros h₁
  rw [Set.subset_def]
  intros a h₂
  rw [Set.ext_iff] at *
  specialize h₁ a
  cases' h₁ with l₁ r₁
  apply r₁ at h₂
  rw [Set.inter_def] at h₂
  rw [Set.mem_def, Set.setOf_app_iff] at h₂
  cases' h₂ with l₂ r₂
  assumption

/-
  Theorem 1.22 (Absorption Laws)
-/

example : A ∪ (A ∩ B) = A := by
  ext x₁
  constructor <;> intros h₁
  case h.mp =>
    rw [Set.inter_def, Set.union_def] at h₁
    rw [Set.mem_def, Set.setOf_app_iff] at h₁
    cases' h₁ with l₁ r₁
    assumption
    cases' r₁ with l₁ r₁
    assumption
  case h.mpr =>
    rw [Set.inter_def, Set.union_def]
    rw [Set.mem_def, Set.setOf_app_iff]
    left
    assumption

example : A ∩ (A ∪ B) = A := by
  ext a
  constructor <;> intros h₁
  . cases' h₁ with l₁ r₁
    assumption
  . constructor
    assumption
    left
    assumption

/-
  Theorem 1.23
-/

example : (Aᶜ)ᶜ = A := by
  ext x₁
  constructor <;> intros h₁
  case h.mp =>
    repeat rw [Set.compl_def] at h₁
    repeat rw [Set.mem_def, Set.setOf_app_iff] at h₁
    by_contra h₂
    apply h₁
    assumption
  case h.mpr =>
    repeat rw [Set.compl_def]
    repeat rw [Set.mem_def, Set.setOf_app_iff]
    by_contra h₂
    apply h₂
    assumption

/-
  Theorem 1.24 (DeMorgan's)
-/

example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  repeat rw [Set.compl_def]
  ext x₁
  constructor <;> intros h₁
  case h.mp =>
    constructor
    case left =>
      repeat rw [Set.mem_def, Set.setOf_app_iff] at *
      rw [Set.union_def] at h₁
      repeat rw [Set.mem_def, Set.setOf_app_iff] at h₁
      by_contra h₂
      apply h₁
      left
      assumption
    case right =>
      repeat rw [Set.mem_def, Set.setOf_app_iff] at *
      by_contra h₂
      apply h₁
      right
      assumption
  case h.mpr =>
    cases' h₁ with l r
    repeat rw [Set.mem_def, Set.setOf_app_iff] at *
    by_contra h
    cases' h with l₂ r₂
    apply l
    assumption
    apply r
    assumption

example : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  repeat rw [Set.compl_def]
  rw [Set.union_def]
  ext x₁
  constructor <;> intros h₁
  case h.mp => sorry
  case h.mpr => sorry

/-
  Theorem 1.26
-/

example : A ∪ ∅ = A := by
  ext x₁
  constructor <;> intros h₁
  cases' h₁ with l r
  . assumption
  . cases' r
  left
  assumption

example : A ∩ ∅ = ∅ := by
  ext x₁
  constructor <;> intros h₁
  cases' h₁ with l r
  . assumption
  . cases' h₁

example : A ∪ Set.univ = Set.univ := by
  ext x₁
  constructor <;> intros h₁
  case h.mp =>
    cases' h₁ with l r
    case inl => exact Set.mem_univ x₁
    case inr => assumption
  case h.mpr =>
    right
    assumption

example : A ∩ Set.univ = A := by
  ext x₁
  constructor <;> intros h₁
  case h.mp =>
    cases' h₁ with l r
    assumption
  case h.mpr =>
    constructor
    assumption
    trivial

example : Set.univᶜ = (∅ : Set X) := by sorry

example : (∅ : Set X)ᶜ = Set.univ := by sorry

example : A ∩ Aᶜ = ∅ := by sorry

example : A ∪ Aᶜ = Set.univ := by sorry

end Set2
