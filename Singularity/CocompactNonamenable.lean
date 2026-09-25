import Singularity.CocompactHyperbolic
import Singularity.TraceNonamenable

/-!
# Spectral gap and hitting law for cocompact groups with infinite boundary orbits

Cocompactness now supplies the hyperbolic element. Under the explicit dynamical
nonelementarity hypothesis that every boundary orbit is infinite, the entire
chain through normalization, free subgroups, and invariant means is discharged.
-/

noncomputable section
open Set Filter OnePoint MeasureTheory
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- A cocompact subgroup with no finite boundary orbit has no invariant mean. -/
theorem cocompact_no_invariantMean (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) : ¬HasInvariantMean Γ := by
  obtain ⟨a, ha⟩ := exists_hyperbolic_of_cocompact Γ (horbit ∞)
  exact fuchsian_no_invariantMean_of_abs_trace Γ a ha horbit

/-- Cocompactness and infinite boundary orbits supply the spectral gap for the actual right walk. -/
theorem rightMarkov_gap_of_cocompact (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    spectralRadius ℂ (rightMarkov s μ) < 1 :=
  rightMarkov_nonamenable_spectral_gap s μ hpos hmass hgen (cocompact_no_invariantMean Γ horbit)

/-- The geometric hitting law exists for a discrete cocompact group with infinite
boundary orbits, without a spectral or hyperbolic-element assumption. -/
theorem exists_real_geometric_hittingLaw_of_cocompact (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)
    (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ) :
    ∃ b : (ℕ → s) → OnePoint ℝ, Measurable b ∧
      (∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
        Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z))
          atTop (nhds (compactBoundaryEmbedding (b ω)))) ∧
      let ν := walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b
      IsProbabilityMeasure ν ∧
      ν = (∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℝ => (g : Γ) • p) ν) ∧
      ∀ g : Γ, Measure.map (fun p : OnePoint ℝ => g • p) ν ≪ ν ∧
        ν ≪ Measure.map (fun p : OnePoint ℝ => g • p) ν := by
  exact exists_real_geometric_hittingLaw_of_nonamenable Γ s μ hpos hmass hgen
    (cocompact_no_invariantMean Γ horbit) z

end Singularity
