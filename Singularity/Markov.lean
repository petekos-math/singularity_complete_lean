import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Positivity

/-!
# The right Markov operator on counting-measure L²

A finite set `s` and nonnegative weights summing to one specify the jump law.
The operator is defined on the actual infinite-dimensional `Lp` space, not a
finite truncation of the group.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]

abbrev GroupL2 (Γ : Type*) [MeasurableSpace Γ] :=
  Lp ℂ 2 (Measure.count : Measure Γ)

/-- Right translation: `f(x) ↦ f(xg)`. -/
def rightTranslation (g : Γ) : GroupL2 Γ →ₗᵢ[ℂ] GroupL2 Γ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x * g)
    (measurePreserving_mul_right Measure.count g)

/-- A finite-support right Markov operator. -/
def rightMarkov (s : Finset Γ) (μ : Γ → ℝ) : GroupL2 Γ →L[ℂ] GroupL2 Γ :=
  ∑ g ∈ s, (μ g : ℂ) • (rightTranslation g).toContinuousLinearMap

/-- Each right translation is an isometry on counting-measure `L²`. -/
theorem rightTranslation_norm (g : Γ) (f : GroupL2 Γ) :
    ‖rightTranslation g f‖ = ‖f‖ :=
  (rightTranslation g).norm_map f

/-- The Markov operator is a contraction. No amenability, symmetry, or
semigroup-generation assumption is needed for this assertion. -/
theorem rightMarkov_contraction (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (f : GroupL2 Γ) : ‖rightMarkov s μ f‖ ≤ ‖f‖ := by
  change ‖(∑ g ∈ s, (μ g : ℂ) • (rightTranslation g).toContinuousLinearMap) f‖ ≤ _
  simp only [sum_apply, smul_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  calc
    ‖∑ g ∈ s, (μ g : ℂ) • rightTranslation g f‖ ≤
        ∑ g ∈ s, ‖(μ g : ℂ) • rightTranslation g f‖ := norm_sum_le _ _
    _ = ∑ g ∈ s, μ g * ‖f‖ := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [norm_smul, rightTranslation_norm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hμ g hg)]
    _ = ‖f‖ := by rw [← Finset.sum_mul, hmass, one_mul]

/-- The corresponding operator-norm bound. -/
theorem rightMarkov_norm_le_one (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) :
    ‖rightMarkov s μ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using rightMarkov_contraction s μ hμ hmass f

/-- The definition has the intended pointwise formula, up to the usual
almost-everywhere identification of `Lp` representatives. -/
theorem rightMarkov_apply_ae (s : Finset Γ) (μ : Γ → ℝ) (f : GroupL2 Γ) :
    (rightMarkov s μ f : Γ → ℂ) =ᵐ[Measure.count]
      fun x => ∑ g ∈ s, (μ g : ℂ) * f (x * g) := by
  simp only [rightMarkov, sum_apply, smul_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  apply (Lp.coeFn_finsetSum s (fun g => (μ g : ℂ) • rightTranslation g f)).trans
  have hterm : ∀ g ∈ s,
      ((μ g : ℂ) • rightTranslation g f : GroupL2 Γ) =ᵐ[Measure.count]
        (fun x => (μ g : ℂ) * f (x * g)) := by
    intro g hg
    exact (Lp.coeFn_smul (μ g : ℂ) (rightTranslation g f)).trans
      ((Lp.coeFn_compMeasurePreserving f
        (measurePreserving_mul_right Measure.count g)).const_smul (μ g : ℂ))
  filter_upwards [eventuallyEq_sum hterm] with x hx
  simpa only [Finset.sum_apply] using hx

end Singularity
