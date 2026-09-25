import Singularity.GreenSeries
import Singularity.MarkovAdjoint
import Singularity.WalkKernel

/-!
# Reflected walks, adjoints, and Green rows

The spectral gap is preserved by taking adjoints. The Green resolvent of the
reflected jump law is the adjoint resolvent, so its kernel is the transposed
original Green kernel. No symmetry of the law is assumed.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Singularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Gelfand's formula and equality of power norms give adjoint invariance of the radius. -/
theorem operator_spectralRadius_adjoint (P : E →L[ℂ] E) :
    spectralRadius ℂ P.adjoint = spectralRadius ℂ P := by
  have he (n : ℕ) : ‖P.adjoint ^ n‖₊ = ‖P ^ n‖₊ := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← star_pow, ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint.nnnorm_map _
  have h := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius P.adjoint
  simp only [he] at h
  exact tendsto_nhds_unique h (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius P)

/-- Taking the adjoint commutes with the Green resolvent. -/
theorem green_adjoint (P : E →L[ℂ] E) : (green P).adjoint = green P.adjoint := by
  change star (Ring.inverse (1 - P)) = Ring.inverse (1 - P.adjoint)
  rw [← Ring.inverse_star, star_sub, star_one, ContinuousLinearMap.star_eq_adjoint]

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]

/-- Reflection preserves the precise operator spectral-gap hypothesis. -/
theorem reflectedMarkov_spectral_gap (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    spectralRadius ℂ (rightMarkov (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)) < 1 := by
  rw [← rightMarkov_adjoint_eq_reflected, operator_spectralRadius_adjoint]
  exact hgap

/-- The reflected Green operator is exactly the adjoint of the original one. -/
theorem reflected_green_operator (s : Finset Γ) (μ : Γ → ℝ) :
    green (rightMarkov (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)) =
      (green (rightMarkov s μ)).adjoint := by
  rw [← rightMarkov_adjoint_eq_reflected, ← green_adjoint]

variable [MeasurableSingletonClass Γ]

/-- The actual adjoint column has the coordinates of the original Green row. -/
theorem green_adjoint_coefficient (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x a : Γ) :
    (green (rightMarkov s μ)).adjoint (countingDelta x) a = (walkGreen s μ x a : ℂ) := by
  rw [← countingDelta_inner a, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm, countingDelta_inner, ← walkGreen_eq_coefficient s μ hgap, Complex.conj_ofReal]

/-- Reflection transposes the path-counting Green kernel. -/
theorem reflected_walkGreen (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    walkGreen (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) x y = walkGreen s μ y x := by
  apply Complex.ofReal_injective
  rw [walkGreen_eq_coefficient _ _ (reflectedMarkov_spectral_gap s μ hgap),
    reflected_green_operator, green_adjoint_coefficient s μ hgap]

end Singularity
