import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Invariance of weighted product measures

These change-of-variables results keep the target-point Radon–Nikodym
convention explicit. They allow infinite total mass and do not assert existence
of hitting measures or of a full Naïm kernel.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Singularity

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Transporting a density by a measurable equivalence composes it with the inverse. -/
theorem map_withDensity_equiv (e : X ≃ᵐ Y) (μ : Measure X)
    (K : X → ℝ≥0∞) (hK : Measurable K) :
    Measure.map e (μ.withDensity K) =
      (Measure.map e μ).withDensity (fun y => K (e.symm y)) := by
  ext A hA
  rw [Measure.map_apply e.measurable hA, withDensity_apply _ (e.measurable hA),
    withDensity_apply _ hA]
  simpa [Function.comp_def] using
    (setLIntegral_map (μ := μ) hA (hK.comp e.symm.measurable) e.measurable).symm

/-- A weighted product is invariant when its transformed kernel cancels the two
pushforward densities. The cancellation can hold almost everywhere. -/
theorem weightedProduct_invariant (e : X ≃ᵐ X) (f : Y ≃ᵐ Y)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (rX : X → ℝ≥0∞) (rY : Y → ℝ≥0∞) (K : X × Y → ℝ≥0∞)
    (hrX : Measurable rX) (hrY : Measurable rY) (hK : Measurable K)
    (hμ : Measure.map e μ = μ.withDensity rX)
    (hν : Measure.map f ν = ν.withDensity rY)
    (hc : ∀ᵐ z ∂μ.prod ν, rX z.1 * rY z.2 * K (e.symm z.1, f.symm z.2) = K z) :
    Measure.map (e.prodCongr f) ((μ.prod ν).withDensity K) =
      (μ.prod ν).withDensity K := by
  rw [map_withDensity_equiv _ _ _ hK]
  have hmap : Measure.map (e.prodCongr f) (μ.prod ν) =
      (Measure.map e μ).prod (Measure.map f ν) :=
    (Measure.map_prod_map μ ν e.measurable f.measurable).symm
  rw [hmap, hμ, hν, prod_withDensity hrX hrY, ← withDensity_mul]
  · exact withDensity_congr_ae hc
  · exact (hrX.comp measurable_fst).mul (hrY.comp measurable_snd)
  · exact hK.comp (e.prodCongr f).symm.measurable

/-- For real kernels, the usual division covariance cancels positive real
pushforward densities. No integrability or finite total mass is required. -/
theorem weightedProduct_invariant_of_div (e : X ≃ᵐ X) (f : Y ≃ᵐ Y)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (rX : X → ℝ) (rY : Y → ℝ) (K : X × Y → ℝ)
    (hrX : Measurable rX) (hrY : Measurable rY) (hK : Measurable K)
    (hpX : ∀ x, 0 < rX x) (hpY : ∀ y, 0 < rY y)
    (hμ : Measure.map e μ = μ.withDensity (fun x => ENNReal.ofReal (rX x)))
    (hν : Measure.map f ν = ν.withDensity (fun y => ENNReal.ofReal (rY y)))
    (hc : ∀ᵐ z ∂μ.prod ν, K (e.symm z.1, f.symm z.2) = K z / (rX z.1 * rY z.2)) :
    Measure.map (e.prodCongr f) ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (K z))) =
      (μ.prod ν).withDensity (fun z => ENNReal.ofReal (K z)) := by
  apply weightedProduct_invariant e f μ ν _ _ _
    hrX.ennreal_ofReal hrY.ennreal_ofReal hK.ennreal_ofReal hμ hν
  filter_upwards [hc] with z hz
  rw [← ENNReal.ofReal_mul (le_of_lt (hpX _)),
    ← ENNReal.ofReal_mul (le_of_lt (mul_pos (hpX _) (hpY _)))]
  congr 1
  rw [hz]
  field_simp [ne_of_gt (hpX z.1), ne_of_gt (hpY z.2)]

end Singularity
