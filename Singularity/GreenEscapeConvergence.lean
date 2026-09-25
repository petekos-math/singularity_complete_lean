import Singularity.GeometricPathConvergence
import Singularity.WeightedOccupation
import Singularity.GreenPoissonBounds

/-!
# Geometric convergence from a lower Green comparison

The spectral gap and a lower bound comparing the Green row with exponential
hyperbolic distance imply almost-sure summable radial decay. Thus the two-sided
Green comparison already used in the rigidity route supplies full geometric
convergence, without an additional convergence hypothesis. The comparison and
spectral gap themselves remain explicit hypotheses.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ]

omit [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] in
/-- The lower half of the distance comparison controls the radial weight by a Green row. -/
theorem radial_le_green_of_comparison (s : Finset Γ) (μ : Γ → ℝ)
    {C : ℝ} (hC : 0 < C) (hcmp : GreenDistanceComparison Γ s μ C) (g : Γ) :
    Real.exp (-dist (g • UpperHalfPlane.I) UpperHalfPlane.I) ≤ C * walkGreen s μ 1 g := by
  have h := mul_le_mul_of_nonneg_left (hcmp 1 g).1 hC.le
  simpa only [one_smul, ← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul,
    dist_comm UpperHalfPlane.I] using h

/-- Expected occupation and the square-summable Green row give summable radial decay. -/
theorem walk_ae_radial_summable_of_comparison [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    {C : ℝ} (hC : 0 < C) (hcmp : GreenDistanceComparison Γ s μ C) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Summable (fun n => Real.exp (-dist (walkPosition s 1 n ω • UpperHalfPlane.I) UpperHalfPlane.I)) :=
  walk_ae_summable_of_le_green s μ hμ hmass hgap 1
    (fun g => Real.exp (-dist (g • UpperHalfPlane.I) UpperHalfPlane.I))
    (fun _ => (Real.exp_pos _).le) C (radial_le_green_of_comparison Γ s μ hC hcmp)

/-- The Green comparison supplies full compact convergence of the actual walk. -/
theorem walk_ae_compact_convergence_of_comparison [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    {C : ℝ} (hC : 0 < C) (hcmp : GreenDistanceComparison Γ s μ C) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      ∃ p : OnePoint ℂ, Tendsto
        (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • UpperHalfPlane.I)) atTop (nhds p) :=
  walk_ae_compact_convergence_of_summable_escape Γ s μ hμ hmass 1 UpperHalfPlane.I
    (walk_ae_radial_summable_of_comparison Γ s μ hμ hmass hgap hC hcmp)

/-- Under the Green comparison, the geometric hitting law needs no assumed path limit. -/
theorem exists_compact_hittingLaw_of_comparison [DiscreteTopology Γ]
    (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    {C : ℝ} (hC : 0 < C) (hcmp : GreenDistanceComparison Γ s μ C) :
    ∃ b : (ℕ → s) → OnePoint ℂ, Measurable b ∧
      (∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
        Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • UpperHalfPlane.I))
          atTop (nhds (b ω))) ∧
      let ν := walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b
      IsProbabilityMeasure ν ∧ ν compactHyperbolicBoundary = 1 ∧
      ν = (∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℂ => (g : Γ) • p) ν) ∧
      ∀ g : Γ, Measure.map (fun p : OnePoint ℂ => g • p) ν ≪ ν ∧
        ν ≪ Measure.map (fun p : OnePoint ℂ => g • p) ν := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  exact exists_compact_geometric_hittingLaw Γ s μ hpos hmass hgen hgap UpperHalfPlane.I
    (walk_ae_compact_convergence_of_comparison Γ s μ (fun g hg => (hpos g hg).le)
      hmass hgap hC hcmp)

end Singularity
