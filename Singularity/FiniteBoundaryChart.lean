import Singularity.RealBoundaryTransport
import Singularity.CompactPoissonMeasure
import Singularity.PoissonDomination

/-!
# Passing from the compact hitting law to its finite real chart

A measurable inverse of the finite chart transfers measures on ℝ ∪ {∞} to ℝ.
Zero mass at infinity gives exact reconstruction. Absolute continuity or a
bounded-density comparison with a compact Poisson measure supplies this condition,
transfers the Poisson bound, and identifies all finite-chart Möbius pushforwards.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The finite real chart is a measurable embedding. -/
theorem measurableEmbedding_realChart : MeasurableEmbedding (fun x : ℝ => (x : OnePoint ℝ)) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding

/-- A measurable coordinate on the finite chart, extended at infinity. -/
def finiteBoundaryCoordinate : OnePoint ℝ → ℝ := measurableEmbedding_realChart.invFun

theorem measurable_finiteBoundaryCoordinate : Measurable finiteBoundaryCoordinate :=
  measurableEmbedding_realChart.measurable_invFun

/-- The coordinate recovers every finite real point exactly. -/
theorem finiteBoundaryCoordinate_coe (x : ℝ) : finiteBoundaryCoordinate (x : OnePoint ℝ) = x :=
  measurableEmbedding_realChart.leftInverse_invFun x

/-- Express a compact-boundary measure in the finite real chart. -/
def finiteBoundaryMeasure (ν : Measure (OnePoint ℝ)) : Measure ℝ :=
  Measure.map finiteBoundaryCoordinate ν

/-- Coordinate transport preserves probabilities. -/
theorem finiteBoundaryMeasure_probability (ν : Measure (OnePoint ℝ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (finiteBoundaryMeasure ν) :=
  (Measure.isProbabilityMeasure_map_iff measurable_finiteBoundaryCoordinate.aemeasurable).mpr
    inferInstance

/-- Lifting a real measure and then taking its finite chart changes nothing. -/
theorem finiteBoundaryMeasure_compactRealMeasure (ν : Measure ℝ) :
    finiteBoundaryMeasure (compactRealMeasure ν) = ν := by
  rw [finiteBoundaryMeasure, compactRealMeasure,
    Measure.map_map measurable_finiteBoundaryCoordinate OnePoint.continuous_coe.measurable]
  have he : finiteBoundaryCoordinate ∘ (fun x : ℝ => (x : OnePoint ℝ)) = id :=
    funext finiteBoundaryCoordinate_coe
  rw [he, Measure.map_id]

/-- Zero mass at infinity is exactly what is needed for reconstruction in the finite chart. -/
theorem finiteBoundaryMeasure_reconstruct (ν : Measure (OnePoint ℝ)) (hinfty : ν {∞} = 0) :
    compactRealMeasure (finiteBoundaryMeasure ν) = ν := by
  have hae : ∀ᵐ p ∂ν, p ≠ (∞ : OnePoint ℝ) := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_eq_eq_singleton] using hinfty
  rw [compactRealMeasure, finiteBoundaryMeasure,
    Measure.map_map OnePoint.continuous_coe.measurable measurable_finiteBoundaryCoordinate]
  calc
    _ = Measure.map id ν := by
      apply Measure.map_congr
      filter_upwards [hae] with p hp
      cases p with
      | infty => exact (hp rfl).elim
      | coe x => exact congrArg (fun y : ℝ => (y : OnePoint ℝ)) (finiteBoundaryCoordinate_coe x)
    _ = ν := Measure.map_id

/-- Absolute continuity with a visual measure rules out mass at infinity. -/
theorem compactPoisson_ac_infty (ν : Measure (OnePoint ℝ)) (z : ℍ)
    (hac : ν ≪ compactPoissonMeasure z) : ν {∞} = 0 :=
  hac (compactPoissonMeasure_infty z)

/-- Compact visual absolute continuity supplies Lebesgue absolute continuity in the real chart. -/
theorem finiteBoundaryMeasure_absolutelyContinuous (ν : Measure (OnePoint ℝ)) (z : ℍ)
    (hac : ν ≪ compactPoissonMeasure z) : finiteBoundaryMeasure ν ≪ volume := by
  have h := hac.map measurable_finiteBoundaryCoordinate
  change finiteBoundaryMeasure ν ≪ finiteBoundaryMeasure (compactRealMeasure (poissonBoundaryMeasure z)) at h
  rw [finiteBoundaryMeasure_compactRealMeasure] at h
  exact h.trans (halfPlanePoissonMeasure_measureClass z.re z.im_pos).1

/-- A compact Poisson measure bound transfers unchanged to the finite chart. -/
theorem finiteBoundaryMeasure_poisson_bound (ν : Measure (OnePoint ℝ)) (z : ℍ) (B : ℝ)
    (hbound : ν ≤ ENNReal.ofReal B • compactPoissonMeasure z) :
    finiteBoundaryMeasure ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z := by
  have h := Measure.map_mono hbound measurable_finiteBoundaryCoordinate
  rw [Measure.map_smul _ measurable_finiteBoundaryCoordinate.aemeasurable] at h
  change finiteBoundaryMeasure ν ≤ ENNReal.ofReal B •
    finiteBoundaryMeasure (compactRealMeasure (poissonBoundaryMeasure z)) at h
  simpa only [finiteBoundaryMeasure_compactRealMeasure] using h

/-- The chart of a compact translate is the existing real Möbius pushforward. -/
theorem finiteBoundaryMeasure_map (ν : Measure (OnePoint ℝ)) (z : ℍ)
    (hac : ν ≪ compactPoissonMeasure z) (g : SL(2, ℝ)) :
    finiteBoundaryMeasure (Measure.map (fun p : OnePoint ℝ => g • p) ν) =
      Measure.map (realBoundaryMobius g) (finiteBoundaryMeasure ν) := by
  have hrec := finiteBoundaryMeasure_reconstruct ν (compactPoisson_ac_infty ν z hac)
  calc
    _ = finiteBoundaryMeasure (Measure.map (fun p : OnePoint ℝ => g • p)
        (compactRealMeasure (finiteBoundaryMeasure ν))) := by rw [hrec]
    _ = _ := by
      rw [compactRealMeasure_map _ (finiteBoundaryMeasure_absolutelyContinuous ν z hac),
        finiteBoundaryMeasure_compactRealMeasure]

/-- Compact stationarity becomes the finite-chart stationarity equation. -/
theorem finiteBoundaryMeasure_stationary (Γ : Subgroup SL(2, ℝ))
    (s : Finset Γ) (μ : Γ → ℝ) (ν : Measure (OnePoint ℝ)) (z : ℍ)
    (hac : ν ≪ compactPoissonMeasure z)
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℝ => (g : Γ) • p) ν) :
    finiteBoundaryMeasure ν = ∑ g : s, ENNReal.ofReal (μ g) •
      Measure.map (realBoundaryMobius (g : SL(2, ℝ))) (finiteBoundaryMeasure ν) := by
  have h := congrArg (Measure.map finiteBoundaryCoordinate) hstat
  rw [Measure.map_finset_sum measurable_finiteBoundaryCoordinate.aemeasurable] at h
  simp only [Measure.map_smul _ measurable_finiteBoundaryCoordinate.aemeasurable] at h
  change finiteBoundaryMeasure ν = _ at h
  nth_rw 1 [h]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact finiteBoundaryMeasure_map ν z hac (g : SL(2, ℝ))

/-- The extracted hitting density satisfies the precise Poisson estimate used by the analysis modules. -/
theorem finiteBoundaryMeasure_density_bound (ν : Measure (OnePoint ℝ)) [IsProbabilityMeasure ν]
    (z : ℍ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ν ≤ ENNReal.ofReal B • compactPoissonMeasure z) :
    ∀ᵐ u ∂volume, ((finiteBoundaryMeasure ν).rnDeriv volume u).toReal ≤
      B * halfPlanePoisson z.re z.im u := by
  have := finiteBoundaryMeasure_probability ν
  exact rnDeriv_le_poisson_of_measure_bound _ z hB (finiteBoundaryMeasure_poisson_bound ν z B hbound)

end Singularity
