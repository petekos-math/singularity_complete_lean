import Singularity.FuchsianMixedDeficitShadows
import Singularity.AEExceptionalShadowCover

/-!
# Almost-everywhere coverage for the concrete mixed deficit shadows

The harmonic exceptional-set hypothesis is formulated modulo hitting-null
sets. This respects the measure-theoretic nature of the Radon–Nikodym
cocycle. Visual convergence and countable parameter selection remain proved
internally, and the output is exactly the almost-everywhere geometric cover.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology
namespace Singularity

/-- Harmonic exceptional convergence modulo null sets is sufficient for the
canonical mixed family. No pointwise regularity of the chosen derivative
representative is assumed. -/
theorem fuchsianMixedDeficitShadow_ae_finite_eventual_cover
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (g : ℕ → Γ) {Z : Set (OnePoint ℝ)} (hZ : Z.Finite)
    (hshrink : ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ R : ℝ,
      ∀ᶠ n in atTop, ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
        g n • ξ ∉ fuchsianGreenDeficitShadow Γ s μ hpos hmass z R (g n) → ξ ∈ U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ N : ℕ, ∃ F : Finset Γ,
      ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
        ∃ a ∈ F, ∀ᶠ n in atTop,
          g (φ n) • (a⁻¹ • ξ) ∈ fuchsianMixedDeficitShadow Γ s μ hpos hmass z N (g (φ n)) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  obtain ⟨φ, hφ, p, hp⟩ := projective_visualShadow_exceptional_subsequence
    (fun n => (g n : PSL(2, ℝ))) z
  have hfinite : (Z ∪ {p}).Finite := hZ.union (finite_singleton p)
  have hescape (ξ : OnePoint ℝ) : ∃ a : Γ, a⁻¹ • ξ ∉ Z ∪ {p} := by
    by_contra hnone
    push Not at hnone
    apply hne.infinite_boundary_orbits Γ ξ
    apply hfinite.subset
    rintro η ⟨a, rfl⟩
    simpa only [inv_inv] using hnone a⁻¹
  refine ⟨φ, hφ, ?_⟩
  apply finite_eventual_cover_of_ae_adjustable_shadows
    (projectiveHittingMeasure Γ s z μ hpos hmass)
    (fun a => (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z a).1)
    (fun N n => (fun ξ : OnePoint ℝ => g (φ n) • ξ) ⁻¹'
      fuchsianMixedDeficitShadow Γ s μ hpos hmass z N (g (φ n)))
    (Z ∪ {p}) hfinite.isClosed hescape
  intro U hU hZU
  obtain ⟨R, hR⟩ := hshrink U hU (subset_union_left.trans hZU)
  obtain ⟨r, hr, hv⟩ := hp U hU (hZU (Or.inr (mem_singleton p)))
  obtain ⟨N, hN⟩ := fuchsianMixedDeficitShadow_cofinal Γ s μ hpos hmass z R hr
  refine ⟨N, ?_⟩
  filter_upwards [hφ.tendsto_atTop.eventually hR, hv] with n hn hvn
  filter_upwards [hn] with ξ hξ hbad
  by_cases hH : g (φ n) • ξ ∈ fuchsianGreenDeficitShadow Γ s μ hpos hmass z R (g (φ n))
  · have hV : g (φ n) • ξ ∉ visualShadow z (g (φ n) • z) r :=
      fun hV => hbad (hN (g (φ n)) ⟨hH, hV⟩)
    exact hvn hV
  · exact hξ hH

end Singularity
