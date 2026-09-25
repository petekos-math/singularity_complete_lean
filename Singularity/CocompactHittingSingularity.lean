import Singularity.OneSidedNaimRigidity
import Singularity.CocompactTwoSidedSingularity

/-!
# Singularity for finite-support cocompact walks without symmetry

The zero-one law upgrades forward nonsingularity to visual absolute continuity.
The actual one-sided Hopf argument then forces reflected absolute continuity.
This contradicts the already checked two-sided Fourier obstruction. The
conclusion concerns the actual hitting distribution, with no current, chart,
normalization, or symmetry assumption left in the theorem statement.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)

include horbit in
/-- The forward hitting measure is singular, with no symmetry assumption on the law. -/
theorem cocompact_hittingMeasure_singular :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z := by
  by_contra hns
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableSpace SL(2, ℝ) := borel _
  let : BorelSpace SL(2, ℝ) := ⟨rfl⟩
  let := slTwo_polishSpace
  let := slTwo_locallyCompactSpace
  let ρ : Measure SL(2, ℝ) := Measure.haar
  have hac := geometricHittingMeasure_absolutelyContinuous_of_not_singular
    Γ s μ hpos hmass hgen hgap z hns
  have hback := reflectedGeometricHittingMeasure_ac_visual_of_forward_ac
    Γ s μ hpos hmass hgen hgap horbit z ρ
    (hac.trans (compactPoissonMeasure_absolutelyContinuous z UpperHalfPlane.I))
  have hsing := (cocompact_forward_or_reflected_singular
    Γ s μ hpos hmass hgen hgap horbit z).resolve_left hns
  let := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact NeZero.ne _ (eq_zero_of_absolutelyContinuous_of_mutuallySingular
    (hback.trans (compactPoissonMeasure_absolutelyContinuous UpperHalfPlane.I z)) hsing)

/-- Cocompactness and infinite boundary orbits supply the spectral gap as well. -/
theorem cocompact_hittingMeasure_singular_of_infinite_orbits :
    geometricHittingMeasure Γ s μ hpos hmass hgen
      (rightMarkov_gap_of_cocompact Γ horbit s μ hpos hmass hgen) z ⟂ₘ compactPoissonMeasure z :=
  cocompact_hittingMeasure_singular Γ s μ hpos hmass hgen
    (rightMarkov_gap_of_cocompact Γ horbit s μ hpos hmass hgen) horbit z

include horbit in
/-- Both forward and reflected hitting laws are singular in the cocompact case. -/
theorem cocompact_forward_and_reflected_singular :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z ∧
      reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z := by
  refine ⟨cocompact_hittingMeasure_singular Γ s μ hpos hmass hgen hgap horbit z, ?_⟩
  exact cocompact_hittingMeasure_singular Γ (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflected_jump_pos s μ hpos) ((reflected_jump_mass s μ).trans hmass)
    (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap) horbit z

end Singularity
