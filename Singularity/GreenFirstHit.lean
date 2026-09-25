import Singularity.FirstEntranceHarmonic
import Singularity.EntranceOperator

/-!
# Singleton first-hit renewal and Green bounds against harmonic functions

The Green column is the first-hit column multiplied by the diagonal Green
entry. This is proved using the established uniqueness of the square-integrable
Dirichlet problem. It turns finite-time stopping bounds into Green inequalities
without identifying the Martin boundary.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- The Green kernel factors through the first hit of its target vertex. -/
theorem walkGreen_first_hit (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    walkGreen s μ x y = firstEntranceKernel s μ {y} x y * walkGreen s μ y y := by
  have he : green (rightMarkov s μ) (countingDelta y) =
      (walkGreen s μ y y : ℂ) • firstEntranceColumn s μ hμ hgap {y} y := by
    apply harmonic_eq_of_boundary_eq (rightMarkov s μ) (rightMarkov_contraction s μ hμ hmass)
      hgap {y}
    · intro v hv
      have hvy : v = y := hv
      subst v
      rw [← walkGreen_eq_coefficient s μ hgap, counting_smul_apply,
        firstEntranceColumn_apply, firstEntranceKernel_of_mem s μ {y} (mem_singleton y)]
      simp
    · intro v hv
      have h := congrArg (countingEvaluation v)
        (green_right_inverse (rightMarkov s μ) hgap (countingDelta y))
      simp only [map_sub, countingEvaluation_apply, countingDelta_apply] at h
      have hvy : v ≠ y := hv
      rw [ite_eq_right_iff.mpr (fun h => (hvy h).elim)] at h
      exact (sub_eq_zero.mp h).symm
    · intro v hv
      rw [map_smul, counting_smul_apply, counting_smul_apply,
        firstEntranceColumn_harmonic s μ hμ hgap {y} y hv]
  have h := congrArg (countingEvaluation x) he
  simp only [countingEvaluation_apply, counting_smul_apply, firstEntranceColumn_apply,
    ← walkGreen_eq_coefficient s μ hgap] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, mul_comm] using h

/-- Every nonnegative superharmonic function bounds the Green kernel after diagonal normalization. -/
theorem walkGreen_superharmonic_bound (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (h : Γ → ℝ) (hp : ∀ x, 0 ≤ h x)
    (hh : ∀ x, ∑ g ∈ s, μ g * h (x * g) ≤ h x) (x y : Γ) :
    walkGreen s μ x y * h y ≤ walkGreen s μ y y * h x := by
  rw [walkGreen_first_hit s μ hμ hmass hgap x y]
  calc
    _ = walkGreen s μ y y * (firstEntranceKernel s μ {y} x y * h y) := by ring
    _ ≤ walkGreen s μ y y * h x := mul_le_mul_of_nonneg_left
      (firstEntrance_superharmonic_bound s μ hμ hgap h hp hh x y)
      (walkGreen_nonneg s μ hμ y y)

end Singularity
