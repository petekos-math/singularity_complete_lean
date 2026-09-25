import Singularity.FiniteBoundaryChart
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
# Singularity and absolute continuity across the boundary models

These equivalences connect the final singularity statement to the actual
projective hitting law, while allowing the analytic contradiction to be carried
out in the finite real chart.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped Classical UpperHalfPlane

namespace Singularity

/-- Singularity of measurable pushforwards implies singularity of the original measures. -/
theorem mutuallySingular_of_measurable_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (μ ν : Measure X)
    (h : Measure.map f μ ⟂ₘ Measure.map f ν) : μ ⟂ₘ ν := by
  refine ⟨f ⁻¹' h.nullSet, h.measurableSet_nullSet.preimage hf, ?_, ?_⟩
  · simpa only [Measure.map_apply hf h.measurableSet_nullSet] using h.measure_nullSet
  · simpa only [Measure.map_apply hf h.measurableSet_nullSet.compl, preimage_compl] using
      h.measure_compl_nullSet

/-- A measurable embedding preserves and reflects mutual singularity. -/
theorem mutuallySingular_map_iff_of_embedding {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y) (hf : MeasurableEmbedding f)
    (μ ν : Measure X) : Measure.map f μ ⟂ₘ Measure.map f ν ↔ μ ⟂ₘ ν :=
  ⟨mutuallySingular_of_measurable_map f hf.measurable μ ν, hf.mutuallySingular_map⟩

/-- Compact real lifting preserves exactly the singularity relation. -/
theorem compactRealMeasure_mutuallySingular_iff (μ ν : Measure ℝ) :
    compactRealMeasure μ ⟂ₘ compactRealMeasure ν ↔ μ ⟂ₘ ν :=
  mutuallySingular_map_iff_of_embedding _ measurableEmbedding_realChart μ ν

/-- Transport between the sphere boundary and real projective line preserves singularity. -/
theorem realProjectiveMeasure_mutuallySingular_iff (μ ν : Measure (OnePoint ℂ))
    (hμ : ∀ᵐ p ∂μ, p ∈ compactHyperbolicBoundary)
    (hν : ∀ᵐ p ∂ν, p ∈ compactHyperbolicBoundary) :
    realProjectiveMeasure μ ⟂ₘ realProjectiveMeasure ν ↔ μ ⟂ₘ ν := by
  have h := mutuallySingular_map_iff_of_embedding compactBoundaryEmbedding
    measurableEmbedding_compactBoundaryEmbedding (realProjectiveMeasure μ) (realProjectiveMeasure ν)
  rw [realProjectiveMeasure_reconstruct μ hμ, realProjectiveMeasure_reconstruct ν hν] at h
  exact h.symm

/-- Taking finite charts preserves singularity when both measures give infinity zero mass. -/
theorem finiteBoundaryMeasure_mutuallySingular_iff (μ ν : Measure (OnePoint ℝ))
    (hμ : μ {∞} = 0) (hν : ν {∞} = 0) :
    finiteBoundaryMeasure μ ⟂ₘ finiteBoundaryMeasure ν ↔ μ ⟂ₘ ν := by
  have h := compactRealMeasure_mutuallySingular_iff (finiteBoundaryMeasure μ) (finiteBoundaryMeasure ν)
  rw [finiteBoundaryMeasure_reconstruct μ hμ, finiteBoundaryMeasure_reconstruct ν hν] at h
  exact h.symm

/-- Singularity against visual measure is equivalent in compact and finite boundary coordinates. -/
theorem finiteBoundaryMeasure_visual_singularity (ν : Measure (OnePoint ℝ))
    (hinfty : ν {∞} = 0) (z : ℍ) :
    finiteBoundaryMeasure ν ⟂ₘ poissonBoundaryMeasure z ↔ ν ⟂ₘ compactPoissonMeasure z := by
  have h := finiteBoundaryMeasure_mutuallySingular_iff ν (compactPoissonMeasure z)
    hinfty (compactPoissonMeasure_infty z)
  simpa only [compactPoissonMeasure, finiteBoundaryMeasure_compactRealMeasure] using h

/-- Real-chart absolute continuity can also be tested after compact lifting. -/
theorem compactRealMeasure_absolutelyContinuous_iff (μ ν : Measure ℝ) :
    compactRealMeasure μ ≪ compactRealMeasure ν ↔ μ ≪ ν := by
  constructor
  · intro h
    have h' := h.map measurable_finiteBoundaryCoordinate
    change finiteBoundaryMeasure (compactRealMeasure μ) ≪
      finiteBoundaryMeasure (compactRealMeasure ν) at h'
    simpa only [finiteBoundaryMeasure_compactRealMeasure] using h'
  · intro h
    exact h.map OnePoint.continuous_coe.measurable

/-- Lebesgue and Poisson measure define the same test for singularity in the finite chart. -/
theorem poissonBoundaryMeasure_singularity_iff (ν : Measure ℝ) (z : ℍ) :
    ν ⟂ₘ poissonBoundaryMeasure z ↔ ν ⟂ₘ volume := by
  have h := halfPlanePoissonMeasure_measureClass z.re z.im_pos
  constructor
  · intro hs
    exact hs.mono_ac Measure.AbsolutelyContinuous.rfl h.2
  · intro hs
    exact hs.mono_ac Measure.AbsolutelyContinuous.rfl h.1

/-- The possible atom at infinity causes no problem for singularity against an atomless reference. -/
theorem finiteBoundaryMeasure_singularity_iff (ν : Measure (OnePoint ℝ)) (η : Measure ℝ)
    (hpoint : η {finiteBoundaryCoordinate (∞ : OnePoint ℝ)} = 0) :
    ν ⟂ₘ compactRealMeasure η ↔ finiteBoundaryMeasure ν ⟂ₘ η := by
  constructor
  · intro hs
    let t : Set ℝ := (fun x : ℝ => (x : OnePoint ℝ)) ⁻¹' hs.nullSet \
      {finiteBoundaryCoordinate (∞ : OnePoint ℝ)}
    have ht : MeasurableSet t :=
      (hs.measurableSet_nullSet.preimage OnePoint.continuous_coe.measurable).diff
        (measurableSet_singleton _)
    refine ⟨t, ht, ?_, ?_⟩
    · rw [finiteBoundaryMeasure, Measure.map_apply measurable_finiteBoundaryCoordinate ht]
      apply measure_mono_null _ hs.measure_nullSet
      intro p hp
      cases p with
      | infty => exact (hp.2 rfl).elim
      | coe x =>
        have hx := hp.1
        change (finiteBoundaryCoordinate (x : OnePoint ℝ) : OnePoint ℝ) ∈ hs.nullSet at hx
        simpa only [finiteBoundaryCoordinate_coe] using hx
    · have hn : η (((fun x : ℝ => (x : OnePoint ℝ)) ⁻¹' hs.nullSet)ᶜ) = 0 := by
        have hn := hs.measure_compl_nullSet
        change (Measure.map (fun x : ℝ => (x : OnePoint ℝ)) η) hs.nullSetᶜ = 0 at hn
        rw [Measure.map_apply OnePoint.continuous_coe.measurable
          hs.measurableSet_nullSet.compl, preimage_compl] at hn
        exact hn
      change η ((_ \ _)ᶜ) = 0
      rw [Set.compl_sdiff]
      exact measure_union_null hpoint hn
  · intro hs
    apply mutuallySingular_of_measurable_map finiteBoundaryCoordinate measurable_finiteBoundaryCoordinate
      ν (compactRealMeasure η)
    change finiteBoundaryMeasure ν ⟂ₘ finiteBoundaryMeasure (compactRealMeasure η)
    simpa only [finiteBoundaryMeasure_compactRealMeasure] using hs

/-- This bridge to the hitting law does not assume zero mass at infinity. -/
theorem compact_hitting_singularity_iff (ν : Measure (OnePoint ℝ)) (z : ℍ) :
    ν ⟂ₘ compactPoissonMeasure z ↔ finiteBoundaryMeasure ν ⟂ₘ volume := by
  have hac : poissonBoundaryMeasure z ≪ volume :=
    (halfPlanePoissonMeasure_measureClass z.re z.im_pos).1
  have hpoint : poissonBoundaryMeasure z {finiteBoundaryCoordinate (∞ : OnePoint ℝ)} = 0 :=
    hac (measure_singleton _)
  exact (finiteBoundaryMeasure_singularity_iff ν (poissonBoundaryMeasure z) hpoint).trans
    (poissonBoundaryMeasure_singularity_iff (finiteBoundaryMeasure ν) z)

end Singularity
