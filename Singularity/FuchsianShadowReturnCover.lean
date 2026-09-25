import Singularity.ConcentratingShadowReturnCover
import Singularity.FuchsianLogCocycle

/-!
# Return-cover construction for the actual Fuchsian hitting law

Nonelementarity supplies orbit escape, and the original walk supplies
quasi-invariance. The remaining inputs are a uniform Green shadow cocycle
estimate, relative concentration in those shadows, and the exceptional-set
convergence after adjusting the shadow parameter.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped MatrixGroups UpperHalfPlane ENNReal Topology

namespace Singularity

/-- A finite corrected return cover for the actual hitting measure follows
from the stated harmonic-shadow and concentration data. These data are
explicit hypotheses and are not asserted to hold in the unrestricted case. -/
theorem fuchsian_shadow_return_cover_from_concentration
    {I : Type*} (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (g : ℕ → Γ) (S : I → ℕ → Set (OnePoint ℝ)) {E Z : Set (OnePoint ℝ)}
    (hS : ∀ i n, MeasurableSet (S i n)) (hE : MeasurableSet E)
    (hpositive : ∀ i n, 0 < projectiveHittingMeasure Γ s z μ hpos hmass (S i n))
    (C : I → ℝ)
    (hbound : ∀ i n, ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
      g n • ξ ∈ S i n →
      |stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) (g n) ξ -
        greenDistance s μ 1 (g n)| ≤ C i)
    (hratio : ∀ i, Tendsto (fun n =>
      (projectiveHittingMeasure Γ s z μ hpos hmass (S i n \ E)).toReal /
        (projectiveHittingMeasure Γ s z μ hpos hmass (S i n)).toReal) atTop (𝓝 0))
    (hZ : Z.Finite)
    (hshrink : ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ i : I,
      ∀ᶠ n in atTop, ((fun ξ : OnePoint ℝ => g n • ξ) ⁻¹' S i n)ᶜ ⊆ U) :
    ∃ i : I, ∃ F : Finset Γ, ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
      ∃ a ∈ F, ∃ n : ℕ, g n • (a⁻¹ • ξ) ∈ S i n ∩ E := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  have hescape (ξ : OnePoint ℝ) : ∃ a : Γ, a⁻¹ • ξ ∉ Z := by
    by_contra hnone
    push Not at hnone
    apply hne.infinite_boundary_orbits Γ ξ
    apply hZ.subset
    rintro η ⟨a, rfl⟩
    simpa only [inv_inv] using hnone a⁻¹
  exact shadow_return_cover_of_adjustable_family
    (projectiveHittingMeasure Γ s z μ hpos hmass)
    (fun a => (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z a).1)
    g S hS hE hpositive (fun n => greenDistance s μ 1 (g n)) C hbound hratio
    hZ.isClosed hescape hshrink

end Singularity
