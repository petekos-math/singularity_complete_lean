import Singularity.KilledWalk

/-!
# Translation of killed paths

Left multiplication preserves the jump word and its weight, while translating
both endpoints and the set to be avoided. The identities hold for finite
coefficients and their Green series without any convergence hypothesis.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Left multiplication transports the avoidance condition by preimage. -/
theorem avoidsBefore_left (s : Finset Γ) (A : Set Γ) (n : ℕ)
    (z x : Γ) (w : WalkWord s n) :
    avoidsBefore s A n (z * x) w ↔
      avoidsBefore s ((fun g => z * g) ⁻¹' A) n x w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [avoidsBefore, mul_assoc, ih, Set.mem_preimage]

/-- The killed transition kernel is covariant under simultaneous left translation. -/
theorem killedWeight_left (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ)
    (n : ℕ) (z x y : Γ) :
    killedWeight s μ A n (z * x) (z * y) =
      killedWeight s μ ((fun g => z * g) ⁻¹' A) n x y := by
  simp only [killedWeight, avoidsBefore_left, walkEndpoint_left,
    mul_left_cancel_iff, Set.mem_preimage]

/-- Left translation also transports the full killed Green series. -/
theorem killedGreen_left (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ)
    (z x y : Γ) :
    killedGreen s μ A (z * x) (z * y) =
      killedGreen s μ ((fun g => z * g) ⁻¹' A) x y := by
  simp only [killedGreen, killedWeight_left]

end Singularity
