import Singularity.FiniteMeasureAbsoluteContinuity
import Singularity.VisualShadowSize

/-!
# Visual shadows for absolutely continuous finite measures

Small complements of inverse shadows and vanishing masses of escaping
shadows transfer to any absolutely continuous finite measure. No essentially
bounded Radon–Nikodym derivative is needed for either conclusion.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped MatrixGroups UpperHalfPlane ENNReal Topology

namespace Singularity

/-- Inverse visual shadows have uniformly almost full mass for every finite
measure absolutely continuous with respect to visual measure. -/
theorem absolutelyContinuous_visualShadow_uniform_full_mass (z : ℍ)
    (ν : Measure (OnePoint ℝ)) [IsFiniteMeasure ν] (hac : ν ≪ compactPoissonMeasure z)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ g : PSL(2, ℝ),
      ν (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r)ᶜ) < ε := by
  let := compactPoissonMeasure_probability z
  obtain ⟨δ, hδ, hsmall⟩ := finiteMeasure_uniform_absoluteContinuity ν
    (compactPoissonMeasure z) hac hε
  obtain ⟨η, hη, hηδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
  have hηr : 0 < (η : ℝ) := by exact_mod_cast hη
  obtain ⟨r, hr, hfull⟩ := projective_visualShadow_uniform_full_mass z hηr
  refine ⟨r, hr, fun g => hsmall _ ?_⟩
  exact (hfull g).trans (by simpa using hηδ)

/-- Escaping visual shadows also have vanishing mass for an absolutely
continuous finite measure. -/
theorem absolutelyContinuous_visualShadow_mass_tendsto_zero (z : ℍ)
    (ν : Measure (OnePoint ℝ)) [IsFiniteMeasure ν] (hac : ν ≪ compactPoissonMeasure z)
    (w : ℕ → ℍ) {r : ℝ} (hr : 0 < r)
    (hescape : Tendsto (fun n => dist z (w n)) atTop atTop) :
    Tendsto (fun n => ν (visualShadow z (w n) r)) atTop (𝓝 0) := by
  let := compactPoissonMeasure_probability z
  exact finiteMeasure_tendsto_zero_of_absolutelyContinuous ν (compactPoissonMeasure z)
    hac (fun n => visualShadow z (w n) r) (visualShadow_mass_tendsto_zero z w hr hescape)

end Singularity
