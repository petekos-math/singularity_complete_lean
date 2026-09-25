import Singularity.RealBoundaryTransport
import Singularity.FuchsianWalkConvergence

/-!
# The random-walk hitting law on the actual real projective boundary

The sphere-valued limit is transported through the inverse of the real boundary
inclusion. The resulting measurable boundary map describes the same path limit
and its law is a stationary probability measure with equivalent group translates.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- The actual random-walk limit and hitting law take values on the compact real boundary. -/
theorem exists_real_geometric_hittingLaw (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ) :
    ∃ b : (ℕ → s) → OnePoint ℝ, Measurable b ∧
      (∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
        Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z))
          atTop (nhds (compactBoundaryEmbedding (b ω)))) ∧
      let ν := walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b
      IsProbabilityMeasure ν ∧
      ν = (∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℝ => (g : Γ) • p) ν) ∧
      ∀ g : Γ, Measure.map (fun p : OnePoint ℝ => g • p) ν ≪ ν ∧
        ν ≪ Measure.map (fun p : OnePoint ℝ => g • p) ν := by
  obtain ⟨b, hb, hl, hp, hboundary, hstat, hequiv⟩ :=
    exists_geometric_hittingLaw Γ s μ hpos hmass hgen hgap z
  let hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  let ν := walkBoundaryLaw s μ hμ hmass b
  have : IsProbabilityMeasure ν := hp
  have hsupp : ∀ᵐ p ∂ν, p ∈ compactHyperbolicBoundary :=
    (mem_ae_iff_prob_eq_one isClosed_compactHyperbolicBoundary.measurableSet).mpr hboundary
  have hpath : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass, b ω ∈ compactHyperbolicBoundary := by
    exact (ae_map_iff hb.aemeasurable isClosed_compactHyperbolicBoundary.measurableSet).mp hsupp
  let b' := compactBoundaryRetraction ∘ b
  have hb' : Measurable b' := measurable_compactBoundaryRetraction.comp hb
  have he : walkBoundaryLaw s μ hμ hmass b' = realProjectiveMeasure ν := by
    change Measure.map b' _ = Measure.map compactBoundaryRetraction (Measure.map b _)
    rw [Measure.map_map measurable_compactBoundaryRetraction hb]
  refine ⟨b', hb', ?_, ?_, ?_, ?_⟩
  · filter_upwards [hl, hpath] with ω hω hpω
    change Tendsto _ atTop (nhds (compactBoundaryEmbedding (compactBoundaryRetraction (b ω))))
    rw [compactBoundaryEmbedding_retraction hpω]
    exact hω
  · rw [show walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b' = realProjectiveMeasure ν from he]
    exact realProjectiveMeasure_probability ν
  · change walkBoundaryLaw s μ hμ hmass b' = _
    rw [he]
    exact realProjectiveMeasure_stationary Γ s μ ν hsupp hstat
  · intro g
    change Measure.map (fun p : OnePoint ℝ => g • p) (walkBoundaryLaw s μ hμ hmass b') ≪ _ ∧ _
    rw [he]
    exact realProjectiveMeasure_translate_equivalent Γ ν hsupp hequiv g

end Singularity
