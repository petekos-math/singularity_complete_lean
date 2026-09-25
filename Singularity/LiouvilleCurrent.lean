import Singularity.LiouvilleBoundaryKernel
import Singularity.BoundaryPairInvariance

/-!
# The concrete Liouville reference current

This is a measure on all ordered distinct projective boundary pairs, not just
the finite real chart. Its explicit continuous positive chordal kernel proves
local finiteness, regularity, sigma-finiteness and nonzero mass. The chart
identity identifies it with dx dy/(x-y)². Group invariance and Hopf ergodicity
are separate statements, not assumed in this construction.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology UpperHalfPlane ENNReal

namespace Singularity

/-- Compact visual probabilities have no point masses, including at infinity. -/
theorem compactPoissonMeasure_nullSingleton (z : ℍ) : NullSingletonClass (compactPoissonMeasure z) := by
  constructor
  intro p
  cases p with
  | infty => exact compactPoissonMeasure_infty z
  | coe x =>
    rw [compactPoissonMeasure, compactRealMeasure,
      Measure.map_apply OnePoint.continuous_coe.measurable (measurableSet_singleton _)]
    have hp : ((↑) : ℝ → OnePoint ℝ) ⁻¹' {(x : OnePoint ℝ)} = {x} := by ext y; simp
    rw [hp]
    exact (halfPlanePoissonMeasure_measureClass z.re z.im_pos).1 (measure_singleton x)

local instance : IsProbabilityMeasure (compactPoissonMeasure UpperHalfPlane.I) := compactPoissonMeasure_probability _
local instance : NullSingletonClass (compactPoissonMeasure UpperHalfPlane.I) := compactPoissonMeasure_nullSingleton _

/-- The Liouville current on ordered distinct geometric endpoints. -/
def compactLiouvilleCurrent : Measure BoundaryPair :=
  boundaryPairCurrent (compactPoissonMeasure UpperHalfPlane.I) (compactPoissonMeasure UpperHalfPlane.I)
    liouvilleBoundaryKernel

theorem compactLiouvilleCurrent_sigmaFinite : SigmaFinite compactLiouvilleCurrent :=
  boundaryPairCurrent_sigmaFinite _ _ _

theorem compactLiouvilleCurrent_locallyFinite : IsLocallyFiniteMeasure compactLiouvilleCurrent :=
  boundaryPairCurrent_locallyFinite _ _ _ continuous_liouvilleBoundaryKernel

theorem compactLiouvilleCurrent_regular : Measure.Regular compactLiouvilleCurrent :=
  boundaryPairCurrent_regular _ _ _ continuous_liouvilleBoundaryKernel

theorem compactLiouvilleCurrent_ne_zero : compactLiouvilleCurrent ≠ 0 :=
  boundaryPairCurrent_ne_zero _ _ _ continuous_liouvilleBoundaryKernel.measurable liouvilleBoundaryKernel_pos

/-- The explicit finite-chart measure, with the null diagonal assigned density zero. -/
def realLiouvilleMeasure : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).prod volume).withDensity (fun p => ENNReal.ofReal (1 / (p.1 - p.2) ^ 2))

theorem realLiouvilleMeasure_sigmaFinite : SigmaFinite realLiouvilleMeasure := by
  unfold realLiouvilleMeasure
  infer_instance

/-- Embedding each real endpoint in the compact boundary square. -/
def realBoundaryPairChart : ℝ × ℝ → OnePoint ℝ × OnePoint ℝ :=
  Prod.map ((↑) : ℝ → OnePoint ℝ) ((↑) : ℝ → OnePoint ℝ)

theorem measurable_realBoundaryPairChart : Measurable realBoundaryPairChart :=
  OnePoint.continuous_coe.measurable.prodMap OnePoint.continuous_coe.measurable

/-- The two visual densities cancel the extended chordal kernel, also on the diagonal. -/
theorem liouvilleBoundaryKernel_chart_density (p : ℝ × ℝ) :
    halfPlanePoisson 0 1 p.1 * halfPlanePoisson 0 1 p.2 *
      extendBoundaryPairKernel liouvilleBoundaryKernel (realBoundaryPairChart p) = 1 / (p.1 - p.2) ^ 2 := by
  by_cases h : p.1 = p.2
  · change _ * extendBoundaryPairKernel liouvilleBoundaryKernel ((p.1 : OnePoint ℝ), (p.2 : OnePoint ℝ)) = _
    rw [h, extendBoundaryPairKernel_diagonal]
    simp
  · change _ * extendBoundaryPairKernel liouvilleBoundaryKernel (finiteBoundaryPair p.1 p.2 h).val = _
    rw [extendBoundaryPairKernel_apply]
    exact liouvilleBoundaryKernel_poisson_density p.1 p.2 h

/-- The concrete compact current has exactly the classical dx dy/(x-y)² chart measure. -/
theorem compactLiouvilleCurrent_chart :
    Measure.map Subtype.val compactLiouvilleCurrent = Measure.map realBoundaryPairChart realLiouvilleMeasure := by
  rw [compactLiouvilleCurrent, boundaryPairCurrent_map _ _ _ continuous_liouvilleBoundaryKernel.measurable]
  let P : ℝ → ℝ := halfPlanePoisson 0 1
  let L := extendBoundaryPairKernel liouvilleBoundaryKernel
  have hL : Measurable L := measurable_extendBoundaryPairKernel _ continuous_liouvilleBoundaryKernel.measurable
  have hP : Measurable P := measurable_halfPlanePoisson 0 1
  have := poissonBoundaryMeasure_probability UpperHalfPlane.I
  have hm : (compactPoissonMeasure UpperHalfPlane.I).prod (compactPoissonMeasure UpperHalfPlane.I) =
      Measure.map realBoundaryPairChart
        ((volume.withDensity (fun x => ENNReal.ofReal (P x))).prod
          (volume.withDensity (fun x => ENNReal.ofReal (P x)))) := by
    exact Measure.map_prod_map _ _ OnePoint.continuous_coe.measurable OnePoint.continuous_coe.measurable
  rw [hm]
  rw [← map_withDensity_comp realBoundaryPairChart measurable_realBoundaryPairChart _ _ hL.ennreal_ofReal]
  have hw := weightedProduct_real_density (volume : Measure ℝ) volume P P
    (L ∘ realBoundaryPairChart) hP hP (hL.comp measurable_realBoundaryPairChart)
    (halfPlanePoisson_nonneg 0 (by norm_num : (0 : ℝ) < 1))
    (halfPlanePoisson_nonneg 0 (by norm_num : (0 : ℝ) < 1))
  simp only [Function.comp_def] at hw ⊢
  rw [hw]
  congr 1
  apply withDensity_congr_ae
  exact Eventually.of_forall (fun p => congrArg ENNReal.ofReal (liouvilleBoundaryKernel_chart_density p))

/-- Marginal absolute continuity with visual measure gives comparison with this concrete current. -/
theorem boundaryPairCurrent_absolutelyContinuous_liouville (μ ν : Measure (OnePoint ℝ)) [SFinite ν]
    (hμ : μ ≪ compactPoissonMeasure UpperHalfPlane.I)
    (hν : ν ≪ compactPoissonMeasure UpperHalfPlane.I) (K : BoundaryPair → ℝ) :
    boundaryPairCurrent μ ν K ≪ compactLiouvilleCurrent :=
  boundaryPairCurrent_absolutelyContinuous _ _ _ _ hμ hν K liouvilleBoundaryKernel
    continuous_liouvilleBoundaryKernel.measurable liouvilleBoundaryKernel_pos

end Singularity
