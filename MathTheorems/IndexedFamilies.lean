import Mathlib.Tactic

namespace IndexedFamilies

variable {α β : Type}
variable (A : β → Set α) -- indexing class
variable (B : Set α)

example : x ∈ ⋃ i, A i ↔ ∃ i : β, x ∈ A i := by exact Set.mem_iUnion

/-
  A Book of Set Theory
  Theorem 1.40(i)
-/

example : (∀ i, A i ⊆ B) → (⋃ (i : β), A i) ⊆ B := by
  intro h₁
  rw [Set.subset_def] at *
  intro x
  rw [Set.mem_iUnion]
  intro h₂
  cases' h₂ with i h₂
  specialize h₁ i
  exact h₁ h₂

/-
  A Book of Set Theory
  Theorem 1.40(ii)
-/

example : (∀ i, B ⊆ A i) → B ⊆ (⋂ (i : β), A i) := by
  intro h₁
  rw [Set.subset_def]
  intro x h₂
  rw [Set.mem_iInter]
  intro i
  specialize h₁ i
  exact h₁ h₂

end IndexedFamilies

namespace PowerSets

variable {α : Type}
variable (A B : Set α)

/-
  A Book of Set Theory
  Exercises 1.7
-/

-- Question #8(a)
example : A ⊆ B ↔ 𝒫 A ⊆ 𝒫 B := by
  repeat rw [Set.subset_def]
  constructor <;> intro h₁
  · intro X h₂
    rw [Set.mem_powerset_iff] at *
    rw [Set.subset_def] at *
    intro x h₃
    specialize h₁ x
    specialize h₂ x
    exact h₁ (h₂ h₃)
  · intro x h₂
    sorry -- todo: unsure how to proceed

-- Question #8(c)
example : 𝒫 (A ∩ B) = 𝒫 A ∩ 𝒫 B := by
  ext X
  constructor <;> intro h₁
  · constructor
    · rw [Set.mem_powerset_iff] at *
      rw [Set.subset_def] at *
      intro x h₂
      specialize h₁ x
      apply h₁ at h₂
      exact Set.mem_of_mem_inter_left h₂
    · rw [Set.mem_powerset_iff] at *
      rw [Set.subset_def] at *
      intro x h₂
      specialize h₁ x
      apply h₁ at h₂
      exact Set.mem_of_mem_inter_right h₂
  · cases' h₁ with h₁ h₂
    rw [Set.mem_powerset_iff] at *
    exact Set.subset_inter h₁ h₂

-- Question #9(a)

example : ⋃₀ (𝒫 A) = A := by
  ext x
  constructor <;> intro h₁
  · rw [Set.mem_sUnion] at h₁
    rcases h₁ with ⟨t, h₁, h₂⟩
    rw [Set.mem_powerset_iff] at h₁
    exact h₁ h₂
  · rw [Set.mem_sUnion]
    use A
    constructor
    · rw [Set.mem_powerset_iff]
    · assumption

end PowerSets
