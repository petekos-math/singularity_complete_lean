import Singularity.CompactBoundary
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Transport from the geometric boundary in the sphere to the real projective line

The boundary inclusion is a measurable embedding. A measurable inverse on its
range transfers supported measures, group translates, stationarity, and measure
classes. Its values off the boundary are irrelevant to supported measures.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical MatrixGroups

namespace Singularity

/-- The compact real boundary inclusion is a closed embedding. -/
theorem isClosedEmbedding_compactBoundaryEmbedding :
    Topology.IsClosedEmbedding compactBoundaryEmbedding :=
  continuous_compactBoundaryEmbedding.isClosedEmbedding compactBoundaryEmbedding_injective

/-- The boundary inclusion is also an embedding of measurable spaces. -/
theorem measurableEmbedding_compactBoundaryEmbedding :
    MeasurableEmbedding compactBoundaryEmbedding :=
  isClosedEmbedding_compactBoundaryEmbedding.measurableEmbedding

/-- A measurable inverse of the boundary inclusion, extended arbitrarily off the boundary. -/
def compactBoundaryRetraction : OnePoint ℂ → OnePoint ℝ :=
  measurableEmbedding_compactBoundaryEmbedding.invFun

theorem measurable_compactBoundaryRetraction : Measurable compactBoundaryRetraction :=
  measurableEmbedding_compactBoundaryEmbedding.measurable_invFun

/-- Retraction recovers every real projective point. -/
theorem compactBoundaryRetraction_embedding (p : OnePoint ℝ) :
    compactBoundaryRetraction (compactBoundaryEmbedding p) = p :=
  measurableEmbedding_compactBoundaryEmbedding.leftInverse_invFun p

/-- On the geometric boundary the inverse also reconstructs the original sphere point. -/
theorem compactBoundaryEmbedding_retraction {p : OnePoint ℂ}
    (hp : p ∈ compactHyperbolicBoundary) :
    compactBoundaryEmbedding (compactBoundaryRetraction p) = p := by
  rw [← compactBoundaryEmbedding_range] at hp
  obtain ⟨q, rfl⟩ := hp
  rw [compactBoundaryRetraction_embedding]

/-- Retraction is equivariant on the geometric boundary. -/
theorem compactBoundaryRetraction_smul (g : SL(2, ℝ)) {p : OnePoint ℂ}
    (hp : p ∈ compactHyperbolicBoundary) :
    compactBoundaryRetraction (g • p) = g • compactBoundaryRetraction p := by
  apply compactBoundaryEmbedding_injective
  rw [compactBoundaryEmbedding_retraction (compactHyperbolicBoundary_smul g hp),
    compactBoundaryEmbedding_smul, compactBoundaryEmbedding_retraction hp]

/-- Express a measure on the sphere boundary as a measure on the real projective line. -/
def realProjectiveMeasure (ν : Measure (OnePoint ℂ)) : Measure (OnePoint ℝ) :=
  Measure.map compactBoundaryRetraction ν

/-- The retraction preserves probability measures. -/
theorem realProjectiveMeasure_probability (ν : Measure (OnePoint ℂ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (realProjectiveMeasure ν) := by
  exact (Measure.isProbabilityMeasure_map_iff measurable_compactBoundaryRetraction.aemeasurable).mpr
    inferInstance

/-- Supported measures can be reconstructed exactly from their real projective transport. -/
theorem realProjectiveMeasure_reconstruct (ν : Measure (OnePoint ℂ))
    (hsupp : ∀ᵐ p ∂ν, p ∈ compactHyperbolicBoundary) :
    Measure.map compactBoundaryEmbedding (realProjectiveMeasure ν) = ν := by
  rw [realProjectiveMeasure, Measure.map_map continuous_compactBoundaryEmbedding.measurable
    measurable_compactBoundaryRetraction]
  calc
    _ = Measure.map id ν := Measure.map_congr (hsupp.mono (fun _ hp => compactBoundaryEmbedding_retraction hp))
    _ = ν := Measure.map_id

/-- Transport commutes with group pushforward for every boundary-supported measure. -/
theorem realProjectiveMeasure_map (ν : Measure (OnePoint ℂ))
    (hsupp : ∀ᵐ p ∂ν, p ∈ compactHyperbolicBoundary) (g : SL(2, ℝ)) :
    realProjectiveMeasure (Measure.map (fun p : OnePoint ℂ => g • p) ν) =
      Measure.map (fun p : OnePoint ℝ => g • p) (realProjectiveMeasure ν) := by
  rw [realProjectiveMeasure, Measure.map_map measurable_compactBoundaryRetraction
    (continuous_const_smul g).measurable, realProjectiveMeasure,
    Measure.map_map (continuous_const_smul g).measurable measurable_compactBoundaryRetraction]
  exact Measure.map_congr (hsupp.mono (fun _ hp => compactBoundaryRetraction_smul g hp))

/-- The finite stationarity equation descends to the real projective boundary. -/
theorem realProjectiveMeasure_stationary (Γ : Subgroup SL(2, ℝ))
    (s : Finset Γ) (μ : Γ → ℝ) (ν : Measure (OnePoint ℂ))
    (hsupp : ∀ᵐ p ∂ν, p ∈ compactHyperbolicBoundary)
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℂ => (g : Γ) • p) ν) :
    realProjectiveMeasure ν = ∑ g : s, ENNReal.ofReal (μ g) •
      Measure.map (fun p : OnePoint ℝ => (g : Γ) • p) (realProjectiveMeasure ν) := by
  have h := congrArg (Measure.map compactBoundaryRetraction) hstat
  rw [Measure.map_finset_sum measurable_compactBoundaryRetraction.aemeasurable] at h
  simp only [Measure.map_smul _ measurable_compactBoundaryRetraction.aemeasurable] at h
  change realProjectiveMeasure ν = _ at h
  nth_rw 1 [h]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact realProjectiveMeasure_map ν hsupp (g : SL(2, ℝ))

/-- Equivalence with every translate is preserved by boundary transport. -/
theorem realProjectiveMeasure_translate_equivalent (Γ : Subgroup SL(2, ℝ))
    (ν : Measure (OnePoint ℂ)) (hsupp : ∀ᵐ p ∂ν, p ∈ compactHyperbolicBoundary)
    (hequiv : ∀ g : Γ, Measure.map (fun p : OnePoint ℂ => g • p) ν ≪ ν ∧
      ν ≪ Measure.map (fun p : OnePoint ℂ => g • p) ν) (g : Γ) :
    Measure.map (fun p : OnePoint ℝ => g • p) (realProjectiveMeasure ν) ≪ realProjectiveMeasure ν ∧
      realProjectiveMeasure ν ≪ Measure.map (fun p : OnePoint ℝ => g • p) (realProjectiveMeasure ν) := by
  have h := hequiv g
  have he := realProjectiveMeasure_map ν hsupp (g : SL(2, ℝ))
  change realProjectiveMeasure (Measure.map (fun p : OnePoint ℂ => g • p) ν) =
    Measure.map (fun p : OnePoint ℝ => g • p) (realProjectiveMeasure ν) at he
  rw [← he]
  exact ⟨h.1.map measurable_compactBoundaryRetraction, h.2.map measurable_compactBoundaryRetraction⟩

end Singularity
