import Singularity.BoundedSequenceShadowRigidity
import Singularity.ReturnCoverDensityRigidity
import Singularity.ShadowRatioRigidity
import Singularity.LogDensityMeasureComparison

/-!
# The measure-theoretic rigidity argument with its geometric inputs exposed

A common shadow family, a positive mass-ratio limit along one sequence, and
a finite corrected return cover imply uniformly comparable magnitudes.
This theorem proves the density upgrade and the final comparison; it does
not construct the shadow family, the differentiating sequence, or the cover.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Singularity

/-- Common exponential shadow estimates, a differentiating sequence, and a
finite corrected return cover imply global magnitude rigidity. All geometric
and differentiation inputs are explicit hypotheses. -/
theorem magnitude_rigidity_of_shadow_return_cover {Γ B : Type*} [Group Γ] [Countable Γ]
    [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
    (ν m : Measure B) [IsFiniteMeasure ν] [IsFiniteMeasure m]
    (hac : ν ≪ m) (hreverse : m ≪ ν)
    (hν : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) ν ≪ ν)
    (hm : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) m ≪ m)
    (S : Γ → Set B) (Dν Dm : Γ → ℝ) (Cν Cm : ℝ)
    (hνl : ∀ a, ENNReal.ofReal (Real.exp (-Dν a - Cν)) ≤ ν (S a))
    (hνu : ∀ a, ν (S a) ≤ ENNReal.ofReal (Real.exp (-Dν a + Cν)))
    (hml : ∀ a, ENNReal.ofReal (Real.exp (-Dm a - Cm)) ≤ m (S a))
    (hmu : ∀ a, m (S a) ≤ ENNReal.ofReal (Real.exp (-Dm a + Cm)))
    (hνshadow : ∀ᵐ ξ ∂ν, ∀ a : Γ, a • ξ ∈ S a →
      |stationaryLogCocycle ν a ξ - Dν a| ≤ Cν)
    (hmshadow : ∀ᵐ ξ ∂ν, ∀ a : Γ, a • ξ ∈ S a →
      |stationaryLogCocycle m a ξ - Dm a| ≤ Cm)
    (g : ℕ → Γ) {ρ : ℝ} (hρ : 0 < ρ)
    (hratio : Tendsto (fun n => (ν (S (g n))).toReal / (m (S (g n))).toReal) atTop (𝓝 ρ))
    (F : Finset Γ) (M J : ℝ)
    (hcorrection : ∀ᵐ ξ ∂ν, ∀ a ∈ F,
      |stationaryLogCocycle ν a ξ - stationaryLogCocycle m a ξ| ≤ J)
    (hcover : ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ,
      g n • (a⁻¹ • ξ) ∈ S (g n) ∧
      |Real.log ((ν.rnDeriv m (g n • (a⁻¹ • ξ))).toReal)| ≤ M) :
    ∃ C : ℝ, ∀ a : Γ, |Dν a - Dm a| ≤ C := by
  obtain ⟨L, hL⟩ := bounded_magnitude_difference_of_shadow_ratio_limit ν m
    (fun n => S (g n)) (fun n => Dν (g n)) (fun n => Dm (g n)) Cν Cm
    (fun n => hνl (g n)) (fun n => hνu (g n))
    (fun n => hml (g n)) (fun n => hmu (g n)) hρ hratio
  exact magnitude_rigidity_of_bounded_sequence_return_cover ν m hac hreverse hν hm
    S Dν Dm Cν Cm hνl hνu hml hmu hνshadow hmshadow g L hL F M J hcorrection hcover

end Singularity
