import Mathlib.Tactic

namespace Topology1

variable {α : Type}
variable [M : MetricSpace α]
variable (p : α) (r : ℝ)

example : IsOpen (Metric.ball p r) := by
  rw [Metric.ball]
  rw [Metric.isOpen_iff]
  intro q h₁
  use (r - dist p q) -- key step: small enough ball
  constructor
  · norm_num
    exact Metric.mem_ball'.mp h₁
  · rw [Metric.ball]
    rw [Set.subset_def]
    intros x h₂
    rw [Set.mem_setOf] at *
    have h₃ : dist x p ≤ dist x q + dist q p := by
      exact dist_triangle x q p
    have h₄ : dist x q + dist q p < r := by
      rw [dist_comm q p]
      exact lt_tsub_iff_right.mp h₂
    exact lt_of_le_of_lt h₃ h₄


end Topology1
