import Singularity.StationaryAtoms
import Singularity.GeometricHittingMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-!
# No point masses for the actual geometric hitting law

Stationarity and infinite boundary orbits imply that the constructed hitting law
vanishes on every singleton. The real chart therefore reconstructs it without
an absolute-continuity assumption. Products of such boundary measures give zero
mass to the diagonal, as required for boundary-pair current constructions.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ)
  (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)

include horbit

/-- The actual geometric hitting law has zero mass on every singleton. -/
theorem geometricHittingMeasure_nullSingleton :
    NullSingletonClass (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) := by
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact stationary_nullSingleton_of_infinite_orbits s μ hpos hmass hgen _
    (geometricHittingMeasure_stationary Γ s μ hpos hmass hgen hgap z) horbit

/-- In particular the constructed hitting law has no atom at the chart's infinity point. -/
theorem geometricHittingMeasure_infty :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z {∞} = 0 := by
  have := geometricHittingMeasure_nullSingleton Γ s μ hpos hmass hgen hgap z horbit
  exact measure_singleton _

/-- The finite real chart exactly reconstructs the actual hitting law, without a density hypothesis. -/
theorem geometricHittingMeasure_chart_reconstruct :
    compactRealMeasure (finiteBoundaryMeasure (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z)) =
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z :=
  finiteBoundaryMeasure_reconstruct _ (geometricHittingMeasure_infty Γ s μ hpos hmass hgen hgap z horbit)

end Singularity

namespace Singularity

/-- The diagonal has zero product mass when the second boundary measure has no point masses. -/
theorem compactBoundary_product_diagonal_null (ν η : Measure (OnePoint ℝ))
    [SFinite η] [NullSingletonClass η] :
    (ν.prod η) {p : OnePoint ℝ × OnePoint ℝ | p.1 = p.2} = 0 := by
  have hm : MeasurableSet {p : OnePoint ℝ × OnePoint ℝ | p.1 = p.2} := measurableSet_diagonal
  rw [Measure.prod_apply hm]
  have hsection (x : OnePoint ℝ) :
      Prod.mk x ⁻¹' {p : OnePoint ℝ × OnePoint ℝ | p.1 = p.2} = {x} := by
    ext y
    simp [eq_comm]
  simp_rw [hsection, measure_singleton]
  exact lintegral_zero

/-- Passing to the finite real chart preserves the absence of point masses. -/
theorem finiteBoundaryMeasure_nullSingleton (ν : Measure (OnePoint ℝ))
    [NullSingletonClass ν] : NullSingletonClass (finiteBoundaryMeasure ν) := by
  constructor
  intro x
  have h := congrArg (fun η : Measure (OnePoint ℝ) => η {(x : OnePoint ℝ)})
    (finiteBoundaryMeasure_reconstruct ν (measure_singleton ∞))
  rw [compactRealMeasure, Measure.map_apply OnePoint.continuous_coe.measurable
    (measurableSet_singleton _)] at h
  have hs : ((↑) : ℝ → OnePoint ℝ) ⁻¹' {(x : OnePoint ℝ)} = {x} := by
    ext y
    simp
  rw [hs] at h
  exact h.trans (measure_singleton _)

end Singularity
