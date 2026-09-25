import Singularity.NormalizedTwoSidedSingularity
import Singularity.ReflectedHittingTransport
import Singularity.NormalizedHittingLaw
import Singularity.ConjugateCocompact
import Singularity.CocompactNonamenable

/-!
# At least one of the two cocompact hitting laws is singular

Cocompactness supplies a hyperbolic element. Conjugating it into diagonal form
preserves the group hypotheses and both hitting-law singularity conclusions.
The normalized Fourier contradiction therefore applies without a coordinate
normalization assumption.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)

include horbit in
/-- For a discrete cocompact group with infinite boundary orbits, the actual
forward or reflected hitting measure is singular against visual measure. -/
theorem cocompact_forward_or_reflected_singular :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z ∨
      reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z := by
  obtain ⟨a, ha⟩ := exists_hyperbolic_of_cocompact Γ (horbit ∞)
  obtain ⟨B, τ, hτ, hdisc, hcompact, hmem⟩ := exists_cocompact_normalized_subgroup Γ a ha
  let Λ := conjugateSubgroup Γ B
  let : DiscreteTopology Λ := hdisc
  let : CompactSpace (Quotient (MulAction.orbitRel Λ ℍ)) := hcompact
  let e : Γ ≃* Λ := (conjugateSubgroupEquiv Γ B).symm
  let t := s.map e.toEmbedding
  let ν : Λ → ℝ := μ ∘ e.symm
  have hν : ∀ g ∈ t, 0 < ν g := mappedSupport_positive e s μ hpos
  have hn : ∑ g ∈ t, ν g = 1 := mappedSupport_mass e s μ hmass
  have hgt : Submonoid.closure (t : Set Λ) = ⊤ := mappedSupport_generates e s hgen
  let : Countable Λ := countable_of_finite_jump_generation t hgt
  let : MeasurableSpace Λ := ⊤
  let : MeasurableSingletonClass Λ := inferInstance
  let : MeasurableMul Λ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  have hrt : spectralRadius ℂ (rightMarkov t ν) < 1 :=
    mappedSupport_spectralGap e s μ hpos hmass hgen (cocompact_no_invariantMean Γ horbit)
  have horbit' (p : OnePoint ℝ) : (MulAction.orbit Λ p).Infinite :=
    (conjugateSubgroup_boundary_orbit_infinite_iff Γ B p).mpr (horbit (B • p))
  let d : Λ := ⟨dilationMatrix τ, hmem⟩
  have hw (g : s) : ν (mappedSupportEquiv e s g) = μ g := by
    change μ (e.symm (e g)) = μ g
    rw [e.symm_apply_apply]
  have haction : ∀ (g : Γ) (w : ℍ), B⁻¹ • (g • w) = e g • (B⁻¹ • w) :=
    conjugateSubgroup_inverse_hyperbolic_action Γ B
  have hf := geometricHittingMeasure_transport_singularity_iff Γ Λ s t (mappedSupportEquiv e s)
    μ ν hpos hν hmass hn hgen hgt hgap hrt hw e.toMonoidHom (fun _ => rfl) B⁻¹ haction z
  have hb := reflectedGeometricHittingMeasure_transport_singularity_iff Γ Λ s t (mappedSupportEquiv e s)
    μ ν hpos hν hmass hn hgen hgt hgap hrt hw e.toMonoidHom (fun _ => rfl) B⁻¹ haction z
  rcases normalized_forward_or_reflected_singular Λ t ν hν hn hgt hrt horbit' (B⁻¹ • z) d rfl hτ with h | h
  · exact Or.inl (hf.mp h)
  · exact Or.inr (hb.mp h)

/-- The spectral gap is also supplied by the cocompact group hypotheses. -/
theorem cocompact_forward_or_reflected_singular_of_infinite_orbits :
    geometricHittingMeasure Γ s μ hpos hmass hgen
      (rightMarkov_gap_of_cocompact Γ horbit s μ hpos hmass hgen) z ⟂ₘ compactPoissonMeasure z ∨
    reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen
      (rightMarkov_gap_of_cocompact Γ horbit s μ hpos hmass hgen) z ⟂ₘ compactPoissonMeasure z :=
  cocompact_forward_or_reflected_singular Γ s μ hpos hmass hgen
    (rightMarkov_gap_of_cocompact Γ horbit s μ hpos hmass hgen) horbit z

end Singularity
