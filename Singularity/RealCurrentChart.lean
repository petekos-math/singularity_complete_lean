import Singularity.BoundaryCurrentDensity
import Singularity.FiniteBoundaryChart

/-!
# Real-chart densities of boundary currents

Actual Lebesgue densities for the two marginals identify the entire finite-chart
current density. Equality with Liouville current transports to the real plane
and then to the two opposite half-lines used in the Fourier argument.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology ENNReal
namespace Singularity

/-- The compact pair kernel, multiplied by the two real marginal densities. -/
def realBoundaryCurrentDensity (q r : ℝ → ℝ) (K : BoundaryPair → ℝ) (p : ℝ × ℝ) : ℝ :=
  q p.1 * r p.2 * extendBoundaryPairKernel K (realBoundaryPairChart p)

theorem measurable_realBoundaryCurrentDensity (q r : ℝ → ℝ) (K : BoundaryPair → ℝ)
    (hq : Measurable q) (hr : Measurable r) (hK : Measurable K) :
    Measurable (realBoundaryCurrentDensity q r K) :=
  (hq.comp measurable_fst |>.mul (hr.comp measurable_snd)).mul
    ((measurable_extendBoundaryPairKernel K hK).comp measurable_realBoundaryPairChart)

theorem realBoundaryCurrentDensity_nonneg (q r : ℝ → ℝ) (K : BoundaryPair → ℝ)
    (hq : ∀ u, 0 ≤ q u) (hr : ∀ u, 0 ≤ r u) (hK : ∀ p, 0 ≤ K p) (p : ℝ × ℝ) :
    0 ≤ realBoundaryCurrentDensity q r K p :=
  mul_nonneg (mul_nonneg (hq _) (hr _)) (extendBoundaryPairKernel_nonneg K hK _)

/-- The real pair chart is a measurable embedding, so it reflects measure equality. -/
theorem measurableEmbedding_realBoundaryPairChart : MeasurableEmbedding realBoundaryPairChart :=
  measurableEmbedding_realChart.prodMap measurableEmbedding_realChart

/-- The actual compact current has its expected real marginal-density formula. -/
theorem boundaryPairCurrent_real_chart (α β : Measure (OnePoint ℝ))
    [SFinite β] [NullSingletonClass β]
    (q r : ℝ → ℝ) (K : BoundaryPair → ℝ)
    (hq : Measurable q) (hr : Measurable r) (hK : Measurable K)
    (hpq : ∀ u, 0 ≤ q u) (hpr : ∀ u, 0 ≤ r u)
    (hα : compactRealMeasure (volume.withDensity (fun u => ENNReal.ofReal (q u))) = α)
    (hβ : compactRealMeasure (volume.withDensity (fun u => ENNReal.ofReal (r u))) = β) :
    Measure.map Subtype.val (boundaryPairCurrent α β K) =
      Measure.map realBoundaryPairChart ((volume.prod volume).withDensity
        (fun p => ENNReal.ofReal (realBoundaryCurrentDensity q r K p))) := by
  rw [boundaryPairCurrent_map α β K hK]
  have hm : α.prod β = Measure.map realBoundaryPairChart
      ((volume.withDensity (fun u => ENNReal.ofReal (q u))).prod
        (volume.withDensity (fun u => ENNReal.ofReal (r u)))) := by
    rw [← hα, ← hβ]
    exact Measure.map_prod_map _ _ OnePoint.continuous_coe.measurable OnePoint.continuous_coe.measurable
  rw [hm, ← map_withDensity_comp realBoundaryPairChart measurable_realBoundaryPairChart _ _
    (measurable_extendBoundaryPairKernel K hK).ennreal_ofReal]
  have hw := weightedProduct_real_density (volume : Measure ℝ) volume q r
    (extendBoundaryPairKernel K ∘ realBoundaryPairChart) hq hr
    ((measurable_extendBoundaryPairKernel K hK).comp measurable_realBoundaryPairChart) hpq hpr
  simp only [Function.comp_def] at hw ⊢
  rw [hw]
  rfl

/-- A compact current comparison gives the exact full real-plane current equality. -/
theorem boundaryPairCurrent_real_eq_liouville (α β : Measure (OnePoint ℝ))
    [SFinite β] [NullSingletonClass β]
    (q r : ℝ → ℝ) (K : BoundaryPair → ℝ)
    (hq : Measurable q) (hr : Measurable r) (hK : Measurable K)
    (hpq : ∀ u, 0 ≤ q u) (hpr : ∀ u, 0 ≤ r u)
    (hα : compactRealMeasure (volume.withDensity (fun u => ENNReal.ofReal (q u))) = α)
    (hβ : compactRealMeasure (volume.withDensity (fun u => ENNReal.ofReal (r u))) = β)
    (c : ℝ≥0∞) (heq : boundaryPairCurrent α β K = c • compactLiouvilleCurrent) :
    (volume.prod volume).withDensity (fun p => ENNReal.ofReal (realBoundaryCurrentDensity q r K p)) =
      c • realLiouvilleMeasure := by
  apply measurableEmbedding_realBoundaryPairChart.map_injective
  rw [← boundaryPairCurrent_real_chart α β q r K hq hr hK hpq hpr hα hβ, heq,
    Measure.map_smul c measurable_subtype_coe.aemeasurable,
    Measure.map_smul c measurable_realBoundaryPairChart.aemeasurable, compactLiouvilleCurrent_chart]

/-- Restricting the chart equality gives exactly the measure identity used by
logarithmic Fourier factorization. -/
theorem realCurrent_eq_liouville_opposite (F : ℝ × ℝ → ℝ) (c : ℝ≥0∞)
    (heq : (volume.prod volume).withDensity (fun p => ENNReal.ofReal (F p)) =
      c • realLiouvilleMeasure) :
    ((volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))).withDensity
      (fun p => ENNReal.ofReal (F p)) =
      c • ((volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))).withDensity
        (fun p => ENNReal.ofReal (realLiouvilleDensity p)) := by
  have h := congrArg (fun ν : Measure (ℝ × ℝ) => ν.restrict (Iio (0 : ℝ) ×ˢ Ioi (0 : ℝ))) heq
  rw [Measure.restrict_smul] at h
  rw [Measure.prod_restrict]
  simpa only [realLiouvilleMeasure, realLiouvilleDensity,
    restrict_withDensity (measurableSet_Iio.prod measurableSet_Ioi)] using h

end Singularity
