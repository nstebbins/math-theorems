import Mathlib.Tactic

namespace Inters

variable {α : Type}
variable (F : Set (Set α))
variable (G : Set (Set α))

example : ⋂₀ (F ∪ G) = ⋂₀ F ∩ ⋂₀ G := by
  ext x
  constructor <;> intro h₁
  · rw [Set.mem_inter_iff]
    repeat rw [Set.mem_sInter] at *
    constructor <;> intro f h₂
    · specialize h₁ f
      apply h₁
      exact Set.mem_union_left G h₂
    · specialize h₁ f
      apply h₁
      exact Set.mem_union_right F h₂
  · rw [Set.mem_inter_iff] at h₁
    repeat rw [Set.mem_sInter] at *
    cases' h₁ with h₁ h₂
    intro t h₃
    cases' h₃ with h₃ h₃
    exact h₁ t (by assumption)
    exact h₂ t (by assumption)

example : A ⊆ ⋂₀ F ↔ ∀ s ∈ F, A ⊆ s := by
  constructor <;> intros h₁
  · intro f h₂
    rw [Set.subset_def]
    intro x h₃
    have h₄ := h₁ h₃
    exact h₄ f h₂
  · rw [Set.subset_def]
    intros x h₂
    rw [Set.mem_sInter]
    intros f h₃
    specialize h₁ f
    apply h₁ at h₃
    exact h₃ h₂

example (h1 : ∀ s ∈ F, A ∪ s ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by sorry

end Inters

namespace Unions

example (A : Set U) : ∃ s, s ⊆ A := by sorry

end Unions
