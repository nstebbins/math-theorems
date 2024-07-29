import Mathlib.Tactic

namespace Function1

/-
  A Book of Set Theory
  Chapter 2.3
-/

variable {X Y Z: Type}
variable (f f₂ : X → Y)
variable (g : Y → Z)
variable (f' : Y → X)

-- note: not exactly the best proof as it's not from first principles
example : f = f₂ ↔ ∀ x : X, f x = f₂ x := by
  constructor <;> intros h₁
  case mp =>
    rw [h₁]
    intros h₁
    rfl
  case mpr =>
    ext x₁
    specialize h₁ x₁
    assumption

/-
  Theorem 2.24
-/

lemma id_def (x : X) : x = id x := by simp

example (h₁ : f' ∘ f = id) : f.Injective := by
  rw [Function.Injective]
  intros x₁ x₂ h₃
  by_contra h₄
  have h₅ : f' (f x₁) = x₁ := by
    nth_rewrite 2 [@id_def X x₁]
    rw [← h₁]
    rfl
  have h₆ : f' (f x₁) = x₂ := by
    nth_rewrite 1 [@id_def X x₂]
    rw [← h₁]
    rw [h₃]
    rfl
  apply h₄
  rw [← h₅]
  rw [← h₆]

example (h₁ : f ∘ f' = id) : f.Surjective := by
  rw [Function.Surjective]
  intros y₁
  use (f' y₁)
  nth_rewrite 2 [@id_def Y y₁]
  rw [← h₁]
  rfl

/-
  Theorem 2.25
-/

example : f.Injective ↔ f.HasLeftInverse := by
  rw [Function.Injective, Function.HasLeftInverse]
  constructor
  . sorry
  . sorry

/-
  Theorem 2.26
-/

example (h₁ : f.Injective) (h₂ : g.Injective) : (g ∘ f).Injective := by
  repeat rw [Function.Injective] at *
  intros x₁ x₂ h₃
  apply h₂ at h₃
  apply h₁ at h₃
  assumption

-- note: i learned how to make the implicit explicit!
lemma inj1 (h₁ : f.Injective) (h₂ : g.Injective) : (g ∘ f).Injective := by
  repeat rw [Function.Injective] at *
  intros x₁ x₂ h₃
  specialize @h₁ x₁ x₂
  specialize @h₂ (f x₁) (f x₂)
  apply h₁
  apply h₂
  assumption

lemma sur1 (h₁ : f.Surjective) (h₂ : g.Surjective) : (g ∘ f).Surjective := by
  repeat rw [Function.Surjective] at *
  intros z₁
  specialize h₂ z₁
  cases' h₂ with y₁ h₂
  specialize h₁ y₁
  cases' h₁ with x₁ h₁
  use x₁
  rw [← h₂]
  rw [← h₁]
  rfl

example (h₁ : f.Bijective) (h₂ : g.Bijective) : (g ∘ f).Bijective := by
  rw [Function.Bijective] at *
  cases' h₁ with l₁ r₁
  cases' h₂ with l₂ r₂
  constructor
  . apply inj1
    repeat assumption
  . apply sur1
    repeat assumption

/-
  Exercises 2.3
-/

/- Question 1 -/

example : id ∘ f = f := by rfl

example : f ∘ id = f := by rfl

/- Question 2 -/

example : (g ∘ f).Injective → f.Injective := by
  repeat rw [Function.Injective]
  intros h₁ a₁ a₂ h₂
  apply h₁
  simp
  rw [h₂]

example : (g ∘ f).Surjective → g.Surjective := by
  repeat rw [Function.Surjective]
  intros h₁ b
  specialize h₁ b
  cases' h₁ with x₁ h₁
  use (f x₁)
  assumption

/- Question 7 -/

example : g.Injective ↔ (g ∘ f = g ∘ f₂) → f = f₂ := by
  constructor
  . intros h₁ h₂
    rw [Function.Injective] at h₁
    sorry
  . sorry
  done

/- Question 8 -/

variable (f : X → Y)
variable (x : X)
variable (g g₂ : Y → Z)

lemma comp_eq : (g ∘ f) x = g (f x) := rfl
#print comp_eq

example : f.Surjective ↔ (g ∘ f = g₂ ∘ f) → g = g₂ := by
  constructor
  . intros h₁ h₂
    rw [Function.Surjective] at h₁
    ext y₁
    specialize h₁ y₁
    cases' h₁ with x₁ h₁
    repeat rw [← h₁]
    rw [← comp_eq f x₁ g]
    rw [h₂]
    rfl
  . intros h₁
    rw [Function.Surjective]
    intros y₁
    sorry

end Function1
