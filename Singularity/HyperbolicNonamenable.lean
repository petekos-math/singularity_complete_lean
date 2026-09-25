import Singularity.DilationNorthSouth
import Singularity.NorthSouthNonamenable
import Singularity.NonamenableHittingLaw

/-!
# Nonamenability and hitting laws from a hyperbolic element

An explicitly conjugated positive dilation supplies uniform north--south dynamics.
If its two endpoints have infinite group orbits, the group contains a free subgroup
and has no invariant mean. The spectral gap and actual geometric hitting law then
follow. Existence of this hyperbolic element from general nonelementarity is not
asserted here.
-/

noncomputable section
open Set Filter OnePoint MeasureTheory
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- A subgroup containing a normalized positive dilation and having infinite endpoint
orbits has no invariant mean. Discreteness is not needed for this group-theoretic conclusion. -/
theorem normalizedFuchsian_no_invariantMean (Γ : Subgroup SL(2, ℝ))
    {t : ℝ} (ht : 0 < t) (ha : dilationMatrix t ∈ Γ)
    (hp : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)
    (hq : (MulAction.orbit Γ ((0 : ℝ) : OnePoint ℝ)).Infinite) : ¬HasInvariantMean Γ := by
  let a : Γ := ⟨dilationMatrix t, ha⟩
  have hdyn : UniformNorthSouth a (∞ : OnePoint ℝ) ((0 : ℝ) : OnePoint ℝ) := by
    intro U hU V hV
    filter_upwards [dilationMatrix_northSouth ht U hU V hV] with n hn
    intro x hx
    exact hn x hx
  exact no_invariantMean_of_northSouth_infinite_orbits (by simp) hdyn hp hq

/-- The same criterion for an arbitrary conjugate of a positive dilation. -/
theorem fuchsian_no_invariantMean_of_hyperbolic (Γ : Subgroup SL(2, ℝ))
    (a : Γ) (b : SL(2, ℝ)) {t : ℝ} (ht : 0 < t)
    (ha : (a : SL(2, ℝ)) = b * dilationMatrix t * b⁻¹)
    (hp : (MulAction.orbit Γ (b • (∞ : OnePoint ℝ))).Infinite)
    (hq : (MulAction.orbit Γ (b • ((0 : ℝ) : OnePoint ℝ))).Infinite) : ¬HasInvariantMean Γ := by
  have hdyn : UniformNorthSouth a (b • (∞ : OnePoint ℝ)) (b • ((0 : ℝ) : OnePoint ℝ)) := by
    intro U hU V hV
    filter_upwards [(dilationMatrix_northSouth ht).conjugate b U hU V hV] with n hn
    intro x hx
    change (a : SL(2, ℝ)) ^ n • x ∈ U
    rw [ha]
    exact hn x hx
  exact no_invariantMean_of_northSouth_infinite_orbits
    (fun h => (by simp : (∞ : OnePoint ℝ) ≠ ((0 : ℝ) : OnePoint ℝ))
      (MulAction.injective b h)) hdyn hp hq

/-- A hyperbolic element with infinite endpoint orbits supplies the original operator gap. -/
theorem rightMarkov_gap_of_hyperbolic (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (a : Γ) (b : SL(2, ℝ)) {t : ℝ} (ht : 0 < t)
    (ha : (a : SL(2, ℝ)) = b * dilationMatrix t * b⁻¹)
    (hp : (MulAction.orbit Γ (b • (∞ : OnePoint ℝ))).Infinite)
    (hq : (MulAction.orbit Γ (b • ((0 : ℝ) : OnePoint ℝ))).Infinite)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    spectralRadius ℂ (rightMarkov s μ) < 1 :=
  rightMarkov_nonamenable_spectral_gap s μ hpos hmass hgen
    (fuchsian_no_invariantMean_of_hyperbolic Γ a b ht ha hp hq)

/-- The actual random-walk limit and hitting law take values on the compact real boundary. -/
theorem exists_real_geometric_hittingLaw_of_hyperbolic (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (a : Γ) (b : SL(2, ℝ)) {t : ℝ} (ht : 0 < t)
    (ha : (a : SL(2, ℝ)) = b * dilationMatrix t * b⁻¹)
    (hp : (MulAction.orbit Γ (b • (∞ : OnePoint ℝ))).Infinite)
    (hq : (MulAction.orbit Γ (b • ((0 : ℝ) : OnePoint ℝ))).Infinite)
    (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (z : ℍ) :
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
    (fuchsian_no_invariantMean_of_hyperbolic Γ a b ht ha hp hq) z

end Singularity
