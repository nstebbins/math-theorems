import Mathlib.Tactic

namespace Inters

variable {α : Type}
variable (F G : Set (Set α))

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

example (h1 : ∀ s ∈ F, A ∪ s ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by
  rw [Set.subset_def]
  intro x h₂
  rw [Set.mem_union]
  rw [Set.mem_sInter] at *
  by_cases h₃ : x ∈ A
  · left; assumption
  · right
    intros f h₄
    specialize h1 f
    specialize h₂ (A ∪ f)
    apply h1 at h₄
    apply h₂ at h₄
    cases' h₄ with h₄ h₄
    · exact False.elim (h₃ h₄)
    · assumption

end Inters

namespace Unions

variable (A B : Set U)
variable (F G : Set (Set U))

example (A : Set U) : ∃ s, s ⊆ A := by
  apply Exists.intro A
  exact fun ⦃a⦄ a ↦ a

example (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  rw [Set.subset_def]
  intro x h₁
  rw [Set.mem_sUnion]
  use A

example (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  rw [Set.subset_def]
  intro x h₂
  rw [Set.mem_sUnion] at *
  rcases h₂ with ⟨f, h₂, h₃⟩
  use f
  constructor
  · exact h1 h₂
  · assumption

example : A ∪ B = ⋃₀ {A, B} := by
  ext x
  constructor <;> intro h₁
  <;> rw [Set.mem_sUnion] at *
  · cases' h₁ with h₁ h₁
    · use A
      constructor
      · exact Set.mem_insert A {B}
      · assumption
    · use B
      constructor
      · exact Set.mem_insert_of_mem A rfl
      · assumption
  · rcases h₁ with ⟨t, h₁, h₂⟩
    cases' h₁ with h₁ h₁
    · rw [← h₁]
      exact Set.mem_union_left B h₂
    · rw [← h₁]
      exact Set.mem_union_right A h₂

example : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x₁
  constructor <;> intro h₁
  <;> rw [Set.mem_union] at *
  <;> rw [Set.mem_sUnion] at *
  · rcases h₁ with ⟨t, h₁, h₂⟩
    cases' h₁ with h₁ h₁
    · left; use t
    · right
      exact Set.mem_sUnion_of_mem h₂ h₁
  · cases' h₁ with h₁ h₁
    · rcases h₁ with ⟨f, h₁, h₂⟩
      use f
      constructor
      · exact Set.mem_union_left G h₁
      · assumption
    · rw [Set.mem_sUnion] at h₁
      rcases h₁ with ⟨t, h₁, h₂⟩
      use t
      constructor
      · exact Set.mem_union_right F h₁
      · assumption

example : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  constructor <;> intro h₁
  · intros f h₂
    rw [Set.subset_def] at *
    intros x h₃
    specialize h₁ x
    rw [Set.mem_sUnion] at h₁
    apply h₁
    use f
  · rw [Set.subset_def]
    intros x h₂
    rw [Set.mem_sUnion] at h₂
    rcases h₂ with ⟨f, h₂, h₃⟩
    specialize h₁ f
    apply h₁ h₂ h₃

example : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  ext x
  constructor <;> intro h₁
  <;> rw [Set.mem_sUnion] at *
  · cases' h₁ with h₁ h₂
    rw [Set.mem_sUnion] at h₂
    rcases h₂ with ⟨t, h₂, h₃⟩
    -- what should s be?
    use (A ∩ t)
    constructor
    · rw [Set.mem_setOf]
      use t
    · exact Set.mem_inter h₁ h₃
  · rcases h₁ with ⟨f, h₁, h₂⟩
    constructor
    · rw [Set.mem_setOf] at h₁
      rcases h₁ with ⟨u, h₁, h₃⟩
      rw [h₃] at h₂
      exact Set.mem_of_mem_inter_left h₂
    · rw [Set.mem_sUnion, Set.mem_setOf] at *
      rcases h₁ with ⟨u, h₁, h₃⟩
      use u
      constructor
      · assumption
      · rw [h₃] at h₂
        exact Set.mem_of_mem_inter_right h₂

end Unions
namespace Combinations

variable (F : Set (Set U))

example : (⋃₀ F)ᶜ = ⋂₀ {s | sᶜ ∈ F} := by
  ext x
  constructor <;> intro h₁
  · rw [Set.mem_sInter]
    intro f h₂
    rw [Set.mem_setOf] at h₂
    by_contra h₃
    apply h₁
    rw [Set.mem_sUnion]
    use (fᶜ)
    constructor
    · assumption
    · assumption
  · rw [Set.mem_sInter] at h₁
    by_contra h₂
    rw [Set.mem_compl_iff] at h₂
    push_neg at h₂
    rw [Set.mem_sUnion] at h₂
    rcases h₂ with ⟨f, h₂, h₃⟩
    sorry -- todo: complete

end Combinations
