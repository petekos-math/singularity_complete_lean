import Singularity.InfiniteWalkProcess
import Singularity.GreenAdjoint
import Singularity.CountingSequence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Weighted occupation and square-summable Green rows

Tonelli identifies the expected accumulated nonnegative vertex weight with its
Green-weighted sum. A finite sum gives almost-sure summability along the actual
sample path. In particular, a weight bounded by a Green row is summable along
the walk under the operator spectral-gap hypothesis.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ]

/-- Every Green row is square summable, since it is an adjoint Green column. -/
theorem walkGreen_row_square_summable (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) :
    Summable (fun y => walkGreen s μ x y ^ 2) := by
  have h := counting_square_summable ((green (rightMarkov s μ)).adjoint (countingDelta x))
  simpa only [green_adjoint_coefficient s μ hgap, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] using h

variable [Countable Γ]

/-- The occupation formula for any nonnegative extended vertex weight. -/
theorem walk_weighted_occupation (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) (f : Γ → ℝ≥0∞) :
    ∫⁻ ω, ∑' n, f (walkPosition s x n ω) ∂infiniteWalkLaw s μ hμ hmass =
      ∑' y, f y * ENNReal.ofReal (walkGreen s μ x y) := by
  rw [lintegral_tsum (f := fun n ω => f (walkPosition s x n ω)) (fun n =>
    ((measurable_of_countable f).comp (measurable_walkPosition s x n)).aemeasurable)]
  have ht (n : ℕ) :
      (∫⁻ ω, f (walkPosition s x n ω) ∂infiniteWalkLaw s μ hμ hmass) =
        ∑' y, f y * ENNReal.ofReal (transitionWeight s μ n x y) := by
    rw [← lintegral_map (measurable_of_countable f) (measurable_walkPosition s x n),
      walkPosition_law, lintegral_countable']
    simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      finiteEndpointLaw_apply]
  simp_rw [ht]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro y
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => transitionWeight_nonneg s μ hμ n x y) (walkGreen_summable s μ hgap x y)]
  rfl

/-- A summable Green-weighted vertex function has summable values on almost every path. -/
theorem walk_ae_summable_weight (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ)
    (f : Γ → ℝ) (hf : ∀ y, 0 ≤ f y)
    (hs : Summable (fun y => f y * walkGreen s μ x y)) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass, Summable (fun n => f (walkPosition s x n ω)) := by
  have hfinite : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      (∑' n, ENNReal.ofReal (f (walkPosition s x n ω))) < ∞ := by
    apply ae_lt_top (Measurable.tsum (fun n =>
      (measurable_of_countable (fun y => ENNReal.ofReal (f y))).comp
        (measurable_walkPosition s x n)))
    change (∫⁻ ω, ∑' n, ENNReal.ofReal (f (walkPosition s x n ω))
      ∂infiniteWalkLaw s μ hμ hmass) ≠ ∞
    rw [walk_weighted_occupation s μ hμ hmass hgap x (fun y => ENNReal.ofReal (f y))]
    simp_rw [← ENNReal.ofReal_mul (hf _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun y => mul_nonneg (hf y) (walkGreen_nonneg s μ hμ x y)) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [hfinite] with ω hω
  have h := ENNReal.summable_toReal hω.ne
  simpa only [ENNReal.toReal_ofReal (hf _)] using h

/-- Domination by a Green row is a sufficient quantitative escape criterion. -/
theorem walk_ae_summable_of_le_green (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ)
    (f : Γ → ℝ) (hf : ∀ y, 0 ≤ f y) (C : ℝ)
    (hbound : ∀ y, f y ≤ C * walkGreen s μ x y) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass, Summable (fun n => f (walkPosition s x n ω)) := by
  apply walk_ae_summable_weight s μ hμ hmass hgap x f hf
  apply ((walkGreen_row_square_summable s μ hgap x).mul_left C).of_nonneg_of_le
    (fun y => mul_nonneg (hf y) (walkGreen_nonneg s μ hμ x y))
  intro y
  simpa only [pow_two, mul_assoc] using
    mul_le_mul_of_nonneg_right (hbound y) (walkGreen_nonneg s μ hμ x y)

end Singularity
