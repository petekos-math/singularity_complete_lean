import Singularity.HyperbolicTraceSquare
import Singularity.HyperbolicNonamenable

/-!
# From a hyperbolic trace to the spectral gap and hitting law

The conjugating matrix and positive dilation parameter are now constructed from
the trace, rather than taken as hypotheses. Infinite boundary orbits then supply
the free-subgroup obstruction to an invariant mean. General existence of a
hyperbolic-trace element remains a separate geometric obligation.
-/

noncomputable section
open Set Filter OnePoint MeasureTheory
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- A subgroup with infinite boundary orbits and an element of hyperbolic trace
has no invariant mean. The diagonalizing conjugacy is constructed internally. -/
theorem fuchsian_no_invariantMean_of_abs_trace (Γ : Subgroup SL(2, ℝ))
    (a : Γ) (htrace : 2 < |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1|)
    (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) : ¬HasInvariantMean Γ := by
  obtain ⟨t, ht, B, hB⟩ := exists_dilation_conjugacy_of_abs_trace (a : SL(2, ℝ)) htrace
  exact fuchsian_no_invariantMean_of_hyperbolic Γ (a ^ 2) B ht hB
    (horbit _) (horbit _)

/-- The hyperbolic trace and infinite boundary orbits imply the original right spectral gap. -/
theorem rightMarkov_gap_of_abs_trace (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (a : Γ) (htrace : 2 < |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1|)
    (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    spectralRadius ℂ (rightMarkov s μ) < 1 :=
  rightMarkov_nonamenable_spectral_gap s μ hpos hmass hgen
    (fuchsian_no_invariantMean_of_abs_trace Γ a htrace horbit)

/-- The actual hitting law follows from the trace and orbit hypotheses, with no
assumed conjugacy, nonamenability, or spectral gap. -/
theorem exists_real_geometric_hittingLaw_of_abs_trace (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (a : Γ) (htrace : 2 < |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1|)
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
    (fuchsian_no_invariantMean_of_abs_trace Γ a htrace horbit) z

end Singularity
