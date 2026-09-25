import Singularity.GeometricNaimQuotient
import Singularity.CocompactHaarAverages

/-!
# Transferring quotient comparison back to boundary currents

The common transversal detects absolute continuity of lattice invariant
measures upstairs. Thus absolute continuity of the actual Naïm quotient
probability with respect to Haar implies absolute continuity of the actual
Naïm current with respect to Liouville. This discharges the measure-class
transfer used after the one-sided Hopf comparison in `OneSidedNaimRigidity`.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

attribute [local instance] slTwo_polishSpace slTwo_locallyCompactSpace cocompact_slTwo_quotient

/-- The common transversal gives the same Haar quotient measure as the earlier construction. -/
theorem compactCosetQuotientMeasure_haar_eq
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (ρ : Measure SL(2, ℝ)) [IsHaarMeasure ρ] :
    compactCosetQuotientMeasure Γ ρ = cocompactHaarQuotientMeasure Γ ρ := by
  let : Countable Γ := countable_of_Lindelof_of_discrete
  let := slTwo_haar_rightInvariant ρ
  exact (compactCosetTransversal_fundamental Γ ρ).quotientMeasure_eq ρ
    (cocompactHaarDomain_fundamental Γ ρ)

/-- Absolute continuity of the distinct-pair measure against Liouville implies
absolute continuity of each probability marginal against visual measure. -/
theorem boundaryPairMeasure_ac_liouville_marginals
    (α β : Measure (OnePoint ℝ)) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    [NullSingletonClass β] (h : boundaryPairMeasure α β ≪ compactLiouvilleCurrent) :
    α ≪ compactPoissonMeasure UpperHalfPlane.I ∧ β ≪ compactPoissonMeasure UpperHalfPlane.I := by
  let := compactPoissonMeasure_probability UpperHalfPlane.I
  let := compactPoissonMeasure_nullSingleton UpperHalfPlane.I
  have hL : compactLiouvilleCurrent ≪
      boundaryPairMeasure (compactPoissonMeasure UpperHalfPlane.I) (compactPoissonMeasure UpperHalfPlane.I) :=
    withDensity_absolutelyContinuous _ _
  have hp := (h.trans hL).map measurable_subtype_coe
  rw [boundaryPairMeasure_map_eq, boundaryPairMeasure_map_eq] at hp
  constructor
  · have hh := hp.map measurable_fst
    simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hh
  · have hh := hp.map measurable_snd
    simpa only [Measure.map_snd_prod, measure_univ, one_smul] using hh

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
  (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)


  (ρ : Measure SL(2, ℝ)) [IsHaarMeasure ρ]

/-- Quotient absolute continuity forces absolute continuity of the actual frame lift. -/
theorem geometricNaimFrameMeasure_ac_haar_of_quotient_ac
    (h : geometricNaimQuotientProbability Γ s μ hpos hmass hgen hgap horbit z ≪
      cocompactHaarQuotientProbability Γ ρ) :
    geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z ≪ ρ := by
  let := geometricNaimFrameMeasure_latticeInvariant Γ s μ hpos hmass hgen hgap horbit z
  let := slTwo_haar_rightInvariant ρ
  apply (compactCosetQuotientMeasure_absolutelyContinuous_iff Γ _ ρ).mp
  rw [compactCosetQuotientMeasure_haar_eq Γ ρ]
  exact (geometricNaimQuotientProbability_measureClass Γ s μ hpos hmass hgen hgap horbit z).2.trans
    (h.trans (cocompactHaarQuotientProbability_measureClass Γ ρ).1)

/-- The resulting frame comparison recovers absolute continuity of the Naïm current. -/
theorem geometricNaimCurrent_ac_liouville_of_quotient_ac
    (h : geometricNaimQuotientProbability Γ s μ hpos hmass hgen hgap horbit z ≪
      cocompactHaarQuotientProbability Γ ρ) :
    geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z ≪ compactLiouvilleCurrent := by
  have hf := geometricNaimFrameMeasure_ac_haar_of_quotient_ac Γ s μ hpos hmass hgen hgap horbit z ρ h
  exact (geometricNaimFrameMeasure_endpoint_measureClass Γ s μ hpos hmass hgen hgap horbit z).2.trans
    ((hf.map measurable_inverseFrameEndpoints).trans (inverseFrameEndpoints_measureClass ρ).1)

/-- Quotient Haar absolute continuity supplies both hitting-marginal inputs for
 the already formalized two-sided Fourier contradiction. -/
theorem geometricHittingMeasures_ac_visual_of_quotient_ac
    (h : geometricNaimQuotientProbability Γ s μ hpos hmass hgen hgap horbit z ≪
      cocompactHaarQuotientProbability Γ ρ) :
    reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪ compactPoissonMeasure UpperHalfPlane.I ∧
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪ compactPoissonMeasure UpperHalfPlane.I := by
  let := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  let := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  let := geometricHittingMeasure_nullSingleton Γ s μ hpos hmass hgen hgap z horbit
  apply boundaryPairMeasure_ac_liouville_marginals
  exact (geometricNaimCurrent_measureClass Γ s μ hpos hmass hgen hgap horbit z).2.trans
    (geometricNaimCurrent_ac_liouville_of_quotient_ac Γ s μ hpos hmass hgen hgap horbit z ρ h)

end Singularity
