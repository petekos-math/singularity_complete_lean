import Singularity.MixedVisualExceptionalLimit
import Singularity.ConcentratingShadowReturnCover

/-!
# Returns through mixed visual shadows

The visual exceptional-point and finite-cover data are supplied by the proved
geometry. The second family's exceptional-set data, its cocycle estimate,
and relative concentration in the mixed shadows remain explicit inputs.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal Topology

namespace Singularity

/-- Mixed-shadow returns with no separate visual convergence or coverage
hypothesis. Relative concentration is required for each fixed pair of shadow
parameters; subsequence extraction preserves those limits. -/
theorem mixed_visualShadow_return_cover_from_concentration {I : Type*}
    (Γ : Subgroup PSL(2, ℝ)) [Countable Γ] (hne : ProjectiveNonelementary Γ)
    (ν : Measure (OnePoint ℝ)) [IsFiniteMeasure ν]
    (hq : ∀ a : Γ, Measure.map (fun ξ : OnePoint ℝ => a • ξ) ν ≪ ν)
    (g : ℕ → Γ) (z : ℍ) (S : I → ℕ → Set (OnePoint ℝ))
    {E Z : Set (OnePoint ℝ)} (hS : ∀ i n, MeasurableSet (S i n))
    (hE : MeasurableSet E) (D : ℕ → ℝ) (C : I → ℝ)
    (hbound : ∀ i n, ∀ᵐ ξ ∂ν, g n • ξ ∈ S i n →
      |stationaryLogCocycle ν (g n) ξ - D n| ≤ C i)
    (hpositive : ∀ i r, 0 < r → ∀ n,
      0 < ν (S i n ∩ visualShadow z (g n • z) r))
    (hratio : ∀ i r, 0 < r → Tendsto (fun n =>
      (ν ((S i n ∩ visualShadow z (g n • z) r) \ E)).toReal /
        (ν (S i n ∩ visualShadow z (g n • z) r)).toReal) atTop (𝓝 0))
    (hZ : Z.Finite)
    (hshrink : ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ i : I,
      ∀ᶠ n in atTop, ((fun ξ : OnePoint ℝ => g n • ξ) ⁻¹' S i n)ᶜ ⊆ U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ i : I, ∃ r : ℝ, 0 < r ∧ ∃ F : Finset Γ,
      ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ,
        g (φ n) • (a⁻¹ • ξ) ∈
          (S i (φ n) ∩ visualShadow z (g (φ n) • z) r) ∩ E := by
  obtain ⟨φ, hφ, i, r, hr, F, hF⟩ :=
    fuchsian_mixed_visualShadow_finite_eventual_cover Γ hne g z S hZ hshrink
  refine ⟨φ, hφ, i, r, hr, F, ?_⟩
  apply shadow_return_cover_of_relative_concentration ν hq
    (fun n => g (φ n))
    (fun n => S i (φ n) ∩ visualShadow z (g (φ n) • z) r)
    (fun n => (hS i (φ n)).inter (isOpen_visualShadow _ _ _).measurableSet)
    hE (fun n => hpositive i r hr (φ n)) (fun n => D (φ n)) (C i)
  · intro n
    filter_upwards [hbound i (φ n)] with ξ hξ
    exact fun hmem => hξ hmem.1
  · exact (hratio i r hr).comp hφ.tendsto_atTop
  · exact Filter.Eventually.of_forall hF

end Singularity
