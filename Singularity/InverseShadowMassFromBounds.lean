import Singularity.CocycleShadowMeasure

/-!
# Positive inverse mass from exponential shadow bounds

A lower exponential mass estimate and a local cocycle estimate already give
a uniform lower bound for inverse-shadow mass. This makes it unnecessary to
assume that lower bound separately when deriving relative concentration.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Singularity

/-- The lower shadow bound and upper local Jacobian bound imply inverse
mass at least exp(-2C), independently of the magnitude D. -/
theorem inverse_shadow_mass_lower_of_exp_bound
    {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
    [MeasurableConstSMul Γ B] (ν : Measure B) [IsFiniteMeasure ν]
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)
    (g : Γ) {S : Set B} (hS : MeasurableSet S) (D C : ℝ)
    (hl : ENNReal.ofReal (Real.exp (-D - C)) ≤ ν S)
    (hbound : ∀ᵐ ξ ∂ν, g • ξ ∈ S → |stationaryLogCocycle ν g ξ - D| ≤ C) :
    Real.exp (-2 * C) ≤ (ν ((fun ξ : B => g • ξ) ⁻¹' S)).toReal := by
  have hu := (shadow_mass_bounds_of_logCocycle ν hq g hS D C hbound).2
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)) (hl.trans hu)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hh
  have hcancel : Real.exp (D - C) * Real.exp (-D + C) = 1 := by
    rw [← Real.exp_add]
    rw [show D - C + (-D + C) = 0 by ring, Real.exp_zero]
  calc
    _ = Real.exp (D - C) * Real.exp (-D - C) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (D - C) * (Real.exp (-D + C) *
        (ν ((fun ξ : B => g • ξ) ⁻¹' S)).toReal) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

end Singularity
