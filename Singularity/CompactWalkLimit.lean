import Singularity.CompactBoundaryEscape
import Singularity.WalkLimitConstruction
import Singularity.ReflectedSupport

/-!
# Conditional construction of the geometric hitting law

All topology, measurability, actions and boundary-support conclusions now refer
to the actual compact sphere and its real projective boundary. The remaining
probabilistic input is existence of almost-sure limits of orbit positions.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Countability supplies joint measurability for the genuine restricted sphere action. -/
theorem measurable_compactSubgroupAction (Γ : Subgroup SL(2, ℝ))
    [Countable Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ] :
    Measurable (fun p : Γ × OnePoint ℂ => p.1 • p.2) :=
  measurable_from_prod_countable_right (fun g => (continuous_const_smul g).measurable)

/-- The orbit map into the sphere is genuinely equivariant. -/
theorem compactOrbit_equivariant (Γ : Subgroup SL(2, ℝ)) (z : ℍ) (g h : Γ) :
    hyperbolicCompactEmbedding ((g * h) • z) = g • hyperbolicCompactEmbedding (h • z) := by
  rw [mul_smul]
  exact hyperbolicCompactEmbedding_smul (g : SL(2, ℝ)) (h • z)

/-- For a discrete Fuchsian subgroup, convergence constructs a stationary probability
law carried by the actual geometric boundary. -/
theorem exists_compact_geometric_hittingLaw (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)
    (hconv : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      ∃ p : OnePoint ℂ,
        Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop (nhds p)) :
    ∃ b : (ℕ → s) → OnePoint ℂ, Measurable b ∧
      (∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
        Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop (nhds (b ω))) ∧
      let ν := walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b
      IsProbabilityMeasure ν ∧ ν compactHyperbolicBoundary = 1 ∧
      ν = (∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℂ => (g : Γ) • p) ν) ∧
      ∀ g : Γ, Measure.map (fun p : OnePoint ℂ => g • p) ν ≪ ν ∧
        ν ≪ Measure.map (fun p : OnePoint ℂ => g • p) ν := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableSMul₂ Γ (OnePoint ℂ) := ⟨measurable_compactSubgroupAction Γ⟩
  let hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨b, hb, hl, hp, hs, he⟩ := exists_stationary_walkLimit s μ hpos hmass hgen
    (fun g : Γ => hyperbolicCompactEmbedding (g • z)) (compactOrbit_equivariant Γ z) hconv
  have hboundary := walkLimit_ae_in_compactBoundary Γ s μ hμ hmass hgap z b hl
  refine ⟨b, hb, hl, hp, ?_, hs, he⟩
  rw [walkBoundaryLaw, Measure.map_apply hb isClosed_compactHyperbolicBoundary.measurableSet]
  exact (mem_ae_iff_prob_eq_one
    (isClosed_compactHyperbolicBoundary.measurableSet.preimage hb)).mp hboundary

end Singularity
