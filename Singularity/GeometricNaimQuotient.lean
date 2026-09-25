import Singularity.GeometricNaimFrameMeasure
import Singularity.CompactCosetMeasure
import Singularity.CocompactGroupQuotient

/-!
# The finite invariant Naïm quotient probability

The actual frame lift is locally finite and right lattice invariant. Restrict
it to the common relatively compact transversal and descend to right cosets.
The quotient measure is finite and nonzero, and its normalization is invariant
under every real time of the geodesic flow. No nonsingularity assumption on
either hitting measure is used.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

attribute [local instance] slTwo_polishSpace slTwo_locallyCompactSpace cocompact_slTwo_quotient

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
  (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)


/-- Descend the actual Naïm frame measure using the common geometric transversal. -/
def geometricNaimQuotientMeasure : Measure (SL(2, ℝ) ⧸ Γ) :=
  compactCosetQuotientMeasure Γ (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z)

/-- The compact quotient has finite Naïm mass. -/
theorem geometricNaimQuotientMeasure_finite :
    IsFiniteMeasure (geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z) := by
  let := geometricNaimFrameMeasure_locallyFinite Γ s μ hpos hmass hgen hgap horbit z
  exact compactCosetQuotientMeasure_finite Γ _

/-- No mass is lost by passing to the common fundamental domain and quotient. -/
theorem geometricNaimQuotientMeasure_ne_zero :
    geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z ≠ 0 := by
  let := geometricNaimFrameMeasure_latticeInvariant Γ s μ hpos hmass hgen hgap horbit z
  exact compactCosetQuotientMeasure_ne_zero Γ _
    (geometricNaimFrameMeasure_ne_zero Γ s μ hpos hmass hgen hgap horbit z)

/-- Every real geodesic-flow time preserves the descended Naïm measure. -/
theorem geometricNaimQuotientMeasure_dilation_invariant (t : ℝ) :
    MeasurePreserving (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix t • x)
      (geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z)
      (geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z) := by
  let := geometricNaimFrameMeasure_latticeInvariant Γ s μ hpos hmass hgen hgap horbit z
  exact compactCosetQuotientMeasure_left_invariant Γ _ (dilationMatrix t)
    (geometricNaimFrameMeasure_dilation_invariant Γ s μ hpos hmass hgen hgap horbit z t)

/-- The normalized actual Naïm probability on the compact right-coset quotient. -/
def geometricNaimQuotientProbability : Measure (SL(2, ℝ) ⧸ Γ) :=
  (geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z univ)⁻¹ •
    geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z

theorem geometricNaimQuotientProbability_probability :
    IsProbabilityMeasure (geometricNaimQuotientProbability Γ s μ hpos hmass hgen hgap horbit z) := by
  let := geometricNaimQuotientMeasure_finite Γ s μ hpos hmass hgen hgap horbit z
  let : NeZero (geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z) :=
    ⟨geometricNaimQuotientMeasure_ne_zero Γ s μ hpos hmass hgen hgap horbit z⟩
  unfold geometricNaimQuotientProbability
  infer_instance

/-- Normalization preserves the quotient measure class. -/
theorem geometricNaimQuotientProbability_measureClass :
    geometricNaimQuotientProbability Γ s μ hpos hmass hgen hgap horbit z ≪
      geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z ∧
    geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z ≪
      geometricNaimQuotientProbability Γ s μ hpos hmass hgen hgap horbit z := by
  let := geometricNaimQuotientMeasure_finite Γ s μ hpos hmass hgen hgap horbit z
  exact ⟨smul_absolutelyContinuous,
    absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))⟩

/-- The actual normalized Naïm probability is invariant under the entire geodesic flow. -/
theorem geometricNaimQuotientProbability_dilation_invariant (t : ℝ) :
    MeasurePreserving (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix t • x)
      (geometricNaimQuotientProbability Γ s μ hpos hmass hgen hgap horbit z)
      (geometricNaimQuotientProbability Γ s μ hpos hmass hgen hgap horbit z) :=
  (geometricNaimQuotientMeasure_dilation_invariant Γ s μ hpos hmass hgen hgap horbit z t).smul_measure _

end Singularity
