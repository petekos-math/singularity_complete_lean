import Singularity.FuchsianShadowPathConcentration
import Singularity.ConcentratedShadowComparison
import Singularity.InverseShadowMassFromBounds

/-!
# Shadow magnitude comparison along actual random-walk paths

Two-sided exponential shadow estimates and local cocycle estimates imply
bounded magnitude discrepancy along almost every path ending in a bounded
log-density window. Both relative concentration inputs follow from the
actual walk law; no mass-ratio limit is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal Topology
namespace Singularity

/-- Geometric shadow data and a bounded-density event give a bounded
magnitude sequence along almost every original walk path ending in the event. -/
theorem fuchsian_shadow_path_magnitude_comparison
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (m : Measure (OnePoint ℝ)) [IsFiniteMeasure m]
    (hνm : projectiveHittingMeasure Γ s z μ hpos hmass ≪ m)
    (hmν : m ≪ projectiveHittingMeasure Γ s z μ hpos hmass)
    (hmq : ∀ a : Γ, Measure.map (fun ξ : OnePoint ℝ => a • ξ) m ≪ m)
    (S : Γ → Set (OnePoint ℝ)) (hS : ∀ a, MeasurableSet (S a))
    (Dν Dm : Γ → ℝ) (Cν Cm : ℝ)
    (hνl : ∀ a, ENNReal.ofReal (Real.exp (-Dν a - Cν)) ≤
      projectiveHittingMeasure Γ s z μ hpos hmass (S a))
    (hνu : ∀ a, projectiveHittingMeasure Γ s z μ hpos hmass (S a) ≤
      ENNReal.ofReal (Real.exp (-Dν a + Cν)))
    (hml : ∀ a, ENNReal.ofReal (Real.exp (-Dm a - Cm)) ≤ m (S a))
    (hmu : ∀ a, m (S a) ≤ ENNReal.ofReal (Real.exp (-Dm a + Cm)))
    (hνshadow : ∀ a, ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
      a • ξ ∈ S a →
        |stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) a ξ - Dν a| ≤ Cν)
    (hmshadow : ∀ a, ∀ᵐ ξ ∂m, a • ξ ∈ S a → |stationaryLogCocycle m a ξ - Dm a| ≤ Cm)
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E) (M : ℝ)
    (hwindow : ∀ ξ ∈ E,
      |Real.log (((projectiveHittingMeasure Γ s z μ hpos hmass).rnDeriv m ξ).toReal)| ≤ M) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      projectiveBoundaryMap Γ s z ω ∈ E →
      ∃ L : ℝ, ∀ n : ℕ, |Dν (walkPosition s 1 n ω) - Dm (walkPosition s 1 n ω)| ≤ L := by
  let ν := projectiveHittingMeasure Γ s z μ hpos hmass
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  have hνq (a : Γ) : Measure.map (fun ξ : OnePoint ℝ => a • ξ) ν ≪ ν :=
    (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z a).1
  have hv := fuchsian_shadow_relative_concentration_along_paths Γ hne s μ hpos hmass hgen z
    ν (Measure.AbsolutelyContinuous.refl ν) hνq S hS Dν Cν (Real.exp_pos (-2 * Cν))
    (fun a => inverse_shadow_mass_lower_of_exp_bound ν hνq a (hS a) (Dν a) Cν (hνl a) (hνshadow a))
    hνshadow hE
  have hm := fuchsian_shadow_relative_concentration_along_paths Γ hne s μ hpos hmass hgen z
    m hmν hmq S hS Dm Cm (Real.exp_pos (-2 * Cm))
    (fun a => inverse_shadow_mass_lower_of_exp_bound m hmq a (hS a) (Dm a) Cm (hml a) (hmshadow a))
    hmshadow hE
  obtain ⟨hl, hu⟩ := restricted_measure_comparison_of_logDensity_window ν m hνm hmν hE M hwindow
  filter_upwards [hv, hm] with ω hωv hωm hmem
  apply bounded_abs_sequence_of_eventually
  exact eventually_bounded_magnitude_difference_of_concentration ν m hE
    (fun n => S (walkPosition s 1 n ω))
    (fun n => Dν (walkPosition s 1 n ω)) (fun n => Dm (walkPosition s 1 n ω))
    Cν Cm M hl hu (fun n => hνl _) (fun n => hνu _) (fun n => hml _) (fun n => hmu _)
    (hωv hmem) (hωm hmem)

end Singularity
