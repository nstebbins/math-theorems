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



end Set2
