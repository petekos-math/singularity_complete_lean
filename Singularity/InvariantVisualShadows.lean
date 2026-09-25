import Singularity.InvariantRestrictionCocycle
import Singularity.VisualShadowCocycle
import Singularity.VisualShadowSize
import Singularity.CocycleShadowMeasure

/-!
# Visual shadow estimates on an invariant carrier

Restriction to a positive-mass invariant measurable set preserves the visual
cocycle and exponential shadow estimates. This addresses the carrier required
for equivalence under nonsingularity, without asserting that the carrier has
full visual mass.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) {E : Set (OnePoint ℝ)}
  (hE : MeasurableSet E)
  (hinv : ∀ g : Γ, (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' E = E)

include hE hinv

/-- The restricted visual measure has the same shadow cocycle error. -/
theorem invariant_visual_logCocycle_shadow_error (g : Γ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ξ ∂(compactPoissonMeasure z).restrict E,
      ξ ∈ (fun η : OnePoint ℝ => g • η) ⁻¹' visualShadow z (g • z) r →
      |stationaryLogCocycle ((compactPoissonMeasure z).restrict E) g ξ - dist z (g • z)| ≤
        Real.log (verticalShadowFactor r) := by
  let := compactPoissonMeasure_probability z
  have hq (a : Γ) : Measure.map (fun ξ : OnePoint ℝ => a • ξ) (compactPoissonMeasure z) ≪
      compactPoissonMeasure z := by
    change Measure.map (fun ξ : OnePoint ℝ => (a : PSL(2, ℝ)) • ξ) (compactPoissonMeasure z) ≪ compactPoissonMeasure z
    rw [compactPoissonMeasure_projective_covariance]
    exact Measure.absolutelyContinuous_of_le_smul (compactPoissonMeasure_le_exp_dist_between (a • z) z)
  filter_upwards [stationaryLogCocycle_invariant_restrict (compactPoissonMeasure z) hE hinv hq g,
    ae_restrict_of_ae (projective_visual_logCocycle_shadow_error (g : PSL(2, ℝ)) z hr)] with ξ he hb hmem
  rw [he]
  exact hb hmem

omit hE hinv in
/-- Restriction can only reduce the inverse-shadow complement mass. -/
theorem restricted_visualShadow_inverse_compl_bound (g : PSL(2, ℝ)) (r : ℝ) :
    ((compactPoissonMeasure z).restrict E)
      (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r)ᶜ) ≤
      ENNReal.ofReal (2 * r / Real.pi) :=
  (Measure.restrict_le_self _).trans (projective_visualShadow_preimage_compl_bound g z r)

/-- The exponential shadow estimate on an invariant carrier retains its
exact inverse-shadow mass. -/
theorem invariant_visualShadow_mass_bounds (g : Γ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (Real.exp (-dist z (g • z) - Real.log (verticalShadowFactor r))) *
      ((compactPoissonMeasure z).restrict E) ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r) ≤
      ((compactPoissonMeasure z).restrict E) (visualShadow z (g • z) r) ∧
    ((compactPoissonMeasure z).restrict E) (visualShadow z (g • z) r) ≤
      ENNReal.ofReal (Real.exp (-dist z (g • z) + Real.log (verticalShadowFactor r))) *
      ((compactPoissonMeasure z).restrict E) ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r) := by
  let := compactPoissonMeasure_probability z
  have hq (a : Γ) : Measure.map (fun ξ : OnePoint ℝ => a • ξ) (compactPoissonMeasure z) ≪
      compactPoissonMeasure z := by
    change Measure.map (fun ξ : OnePoint ℝ => (a : PSL(2, ℝ)) • ξ) (compactPoissonMeasure z) ≪ compactPoissonMeasure z
    rw [compactPoissonMeasure_projective_covariance]
    exact Measure.absolutelyContinuous_of_le_smul (compactPoissonMeasure_le_exp_dist_between (a • z) z)
  exact shadow_mass_bounds_of_logCocycle ((compactPoissonMeasure z).restrict E)
    (invariant_restrict_quasiInvariant _ hE hinv hq) g (isOpen_visualShadow _ _ _).measurableSet
    (dist z (g • z)) (Real.log (verticalShadowFactor r))
    (invariant_visual_logCocycle_shadow_error Γ z hE hinv g hr)

omit hE hinv in
/-- Every positive-mass invariant carrier admits shadows with inverse mass
at least half its total mass, uniformly for the whole subgroup. -/
theorem invariant_visualShadow_uniform_half_mass (hpos : 0 < compactPoissonMeasure z E) :
    ∃ r : ℝ, 0 < r ∧ ∀ g : Γ,
      compactPoissonMeasure z E / 2 ≤ ((compactPoissonMeasure z).restrict E)
        ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r) := by
  let := compactPoissonMeasure_probability z
  have hp : 0 < (compactPoissonMeasure z E).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  obtain ⟨r, hr, hfull⟩ := projective_visualShadow_uniform_full_mass z (div_pos hp (by norm_num : (0 : ℝ) < 2))
  refine ⟨r, hr, fun g => ?_⟩
  let mE := (compactPoissonMeasure z).restrict E
  let T := (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r
  have hT : MeasurableSet T := (isOpen_visualShadow _ _ _).measurableSet.preimage (measurable_const_smul g)
  have hc : mE Tᶜ ≤ compactPoissonMeasure z E / 2 := by
    apply (Measure.restrict_le_self Tᶜ).trans
    apply (hfull (g : PSL(2, ℝ))).le.trans_eq
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    norm_num
  have hu : mE univ = compactPoissonMeasure z E := by simp [mE]
  calc
    compactPoissonMeasure z E / 2 = compactPoissonMeasure z E - compactPoissonMeasure z E / 2 :=
      (ENNReal.sub_half (measure_ne_top _ _)).symm
    _ ≤ compactPoissonMeasure z E - mE Tᶜ := tsub_le_tsub_left hc _
    _ = mE T := by
      rw [← hu, ← measure_compl hT.compl (measure_ne_top _ _)]
      simp

end Singularity
