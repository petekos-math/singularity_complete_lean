import Singularity.FuchsianBoundaryConcentration
import Singularity.MixedVisualExceptionalLimit
import Singularity.TranslatedConcentrationReturnCover

/-!
# Corrected shadow returns along the original random walk

Boundary-event concentration supplies all return-error estimates on paths
ending in the selected event. Visual coverage is proved geometrically; for
mixed shadows only the second family's exceptional-set convergence is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology
namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hgen

/-- Almost every path ending in E supplies a subsequence and finitely many
corrections whose visual shadows return almost every boundary point to E. -/
theorem fuchsian_visualShadow_path_return_cover {E : Set (OnePoint ℝ)}
    (hE : MeasurableSet E) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      projectiveBoundaryMap Γ s z ω ∈ E →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ r : ℝ, 0 < r ∧ ∃ F : Finset Γ,
        ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
          ∃ a ∈ F, ∃ n : ℕ, walkPosition s 1 (φ n) ω • (a⁻¹ • ξ) ∈
            visualShadow z (walkPosition s 1 (φ n) ω • z) r ∩ E := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  filter_upwards [fuchsian_hittingMeasure_complement_concentration
    Γ hne s μ hpos hmass hgen z hE] with ω hω hmem
  obtain ⟨φ, hφ, r, hr, F, hF⟩ := fuchsian_visualShadow_finite_eventual_cover
    Γ hne (fun n => walkPosition s 1 n ω) z
  refine ⟨φ, hφ, r, hr, F, ?_⟩
  exact shadow_return_cover_of_translated_concentration
    (projectiveHittingMeasure Γ s z μ hpos hmass)
    (fun a => (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z a).1)
    (fun n => walkPosition s 1 (φ n) ω)
    (fun n => visualShadow z (walkPosition s 1 (φ n) ω • z) r) E F
    ((hω hmem).comp hφ.tendsto_atTop) (Filter.Eventually.of_forall hF)

/-- For mixed shadows, boundary concentration removes all relative-error and
cocycle hypotheses from the return-cover construction. The second family's
finite exceptional-set convergence remains a geometric input. -/
theorem fuchsian_mixed_visualShadow_path_return_cover {I : Type*}
    (S : I → Γ → Set (OnePoint ℝ)) {E Z : Set (OnePoint ℝ)}
    (hE : MeasurableSet E) (hZ : Z.Finite)
    (hshrink : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ i : I,
        ∀ᶠ n in atTop, ((fun ξ : OnePoint ℝ => walkPosition s 1 n ω • ξ) ⁻¹'
          S i (walkPosition s 1 n ω))ᶜ ⊆ U) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      projectiveBoundaryMap Γ s z ω ∈ E →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ i : I, ∃ r : ℝ, 0 < r ∧ ∃ F : Finset Γ,
        ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
          ∃ a ∈ F, ∃ n : ℕ, walkPosition s 1 (φ n) ω • (a⁻¹ • ξ) ∈
            (S i (walkPosition s 1 (φ n) ω) ∩
              visualShadow z (walkPosition s 1 (φ n) ω • z) r) ∩ E := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  filter_upwards [fuchsian_hittingMeasure_complement_concentration
    Γ hne s μ hpos hmass hgen z hE, hshrink] with ω hω hS hmem
  obtain ⟨φ, hφ, i, r, hr, F, hF⟩ := fuchsian_mixed_visualShadow_finite_eventual_cover
    Γ hne (fun n => walkPosition s 1 n ω) z
    (fun i n => S i (walkPosition s 1 n ω)) hZ hS
  refine ⟨φ, hφ, i, r, hr, F, ?_⟩
  exact shadow_return_cover_of_translated_concentration
    (projectiveHittingMeasure Γ s z μ hpos hmass)
    (fun a => (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z a).1)
    (fun n => walkPosition s 1 (φ n) ω)
    (fun n => S i (walkPosition s 1 (φ n) ω) ∩
      visualShadow z (walkPosition s 1 (φ n) ω • z) r) E F
    ((hω hmem).comp hφ.tendsto_atTop) (Filter.Eventually.of_forall hF)

end Singularity
