import Singularity.CocycleShadowMeasure

/-!
# Green bounds on translated stationary measures

Optional stopping bounds the actual stationary cocycle in both directed
Green distances. Integrating gives bounds on the mass of every image set,
without identifying the boundary with the Martin boundary.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ] [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (ν : Measure B) [IsFiniteMeasure ν]
  (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν)

include hpos hmass hgen hgap hstat

/-- Every measurable image has mass bounded by the forward and backward
hitting probabilities encoded by the directed Green distances. -/
theorem stationary_smul_image_green_bounds (g : Γ) {E : Set B} (hE : MeasurableSet E) :
    ENNReal.ofReal (Real.exp (-greenDistance s μ 1 g)) * ν E ≤ ν ((fun ξ : B => g • ξ) '' E) ∧
      ν ((fun ξ : B => g • ξ) '' E) ≤ ENNReal.ofReal (Real.exp (greenDistance s μ g 1)) * ν E := by
  let D := (greenDistance s μ 1 g - greenDistance s μ g 1) / 2
  let C := (greenDistance s μ 1 g + greenDistance s μ g 1) / 2
  have hb : ∀ᵐ ξ ∂ν, ξ ∈ E → |stationaryLogCocycle ν g ξ - D| ≤ C := by
    filter_upwards [stationaryLogCocycle_ae_green_bounds s μ hpos hgen ν hstat hmass hgap] with ξ hξ _
    apply abs_le.mpr
    dsimp [D, C]
    constructor <;> linarith [(hξ g).1, (hξ g).2]
  have h := measure_smul_image_bounds_of_logCocycle ν
    (fun g => (stationary_translate_equivalent s μ hpos hgen ν hstat g).1) g hE D C hb
  have hl : -D - C = -greenDistance s μ 1 g := by dsimp [D, C]; ring
  have hu : -D + C = greenDistance s μ g 1 := by dsimp [D, C]; ring
  simpa only [hl, hu] using h

/-- The same estimate for a target set retains its inverse-image mass. -/
theorem stationary_set_green_bounds (g : Γ) {S : Set B} (hS : MeasurableSet S) :
    ENNReal.ofReal (Real.exp (-greenDistance s μ 1 g)) * ν ((fun ξ : B => g • ξ) ⁻¹' S) ≤ ν S ∧
      ν S ≤ ENNReal.ofReal (Real.exp (greenDistance s μ g 1)) * ν ((fun ξ : B => g • ξ) ⁻¹' S) := by
  have h := stationary_smul_image_green_bounds s μ hpos hmass hgen hgap ν hstat g
    (hS.preimage (measurable_const_smul g))
  simpa only [image_preimage_eq _ (MulAction.surjective g)] using h

end Singularity
