import Singularity.ReturnCoverDensityRigidity
import Singularity.LogDensityMeasureComparison
import Singularity.ShadowMagnitudeComparison

/-!
# Global shadow rigidity from a bounded comparison sequence

The density-upgrade argument only needs bounded magnitude discrepancy along
one return sequence. A positive mass-ratio limit is one possible source of
this bound, but is not needed in this formulation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Singularity

/-- A bounded magnitude sequence and corrected returns upgrade local shadow
comparison to global magnitude rigidity. -/
theorem magnitude_rigidity_of_bounded_sequence_return_cover {Γ B : Type*} [Group Γ] [Countable Γ]
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
    (g : ℕ → Γ) (L : ℝ) (hL : ∀ n, |Dν (g n) - Dm (g n)| ≤ L)
    (F : Finset Γ) (M J : ℝ)
    (hcorrection : ∀ᵐ ξ ∂ν, ∀ a ∈ F,
      |stationaryLogCocycle ν a ξ - stationaryLogCocycle m a ξ| ≤ J)
    (hcover : ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ,
      g n • (a⁻¹ • ξ) ∈ S (g n) ∧
      |Real.log ((ν.rnDeriv m (g n • (a⁻¹ • ξ))).toReal)| ≤ M) :
    ∃ C : ℝ, ∀ a : Γ, |Dν a - Dm a| ≤ C := by
  let T : ℕ → Set B := fun n => (fun ξ : B => g n • ξ) ⁻¹' S (g n)
  have hv : ∀ᵐ ξ ∂ν, ∀ n, ξ ∈ T n → |stationaryLogCocycle ν (g n) ξ - Dν (g n)| ≤ Cν := by
    filter_upwards [hνshadow] with ξ hξ
    exact fun n hn => hξ (g n) hn
  have hm' : ∀ᵐ ξ ∂ν, ∀ n, ξ ∈ T n → |stationaryLogCocycle m (g n) ξ - Dm (g n)| ≤ Cm := by
    filter_upwards [hmshadow] with ξ hξ
    exact fun n hn => hξ (g n) hn
  have hc : ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ, a⁻¹ • ξ ∈ T n ∩ T n ∧
      |Real.log ((ν.rnDeriv m (g n • (a⁻¹ • ξ))).toReal)| ≤ M := by
    filter_upwards [hcover] with ξ hξ
    obtain ⟨a, ha, n, hn, hw⟩ := hξ
    exact ⟨a, ha, n, ⟨hn, hn⟩, hw⟩
  have hbound := logDensity_bound_of_shadow_return_cover ν m hac hν hm g T T
    (fun n => Dν (g n)) (fun n => Dm (g n)) F Cν Cm L M J hv hm' hL hcorrection hc
  obtain ⟨hl, hu⟩ := measure_exp_comparison_of_logDensity_bound ν m hac hreverse
    (M + Cν + Cm + L + J) hbound
  refine ⟨Cν + Cm + (M + Cν + Cm + L + J), fun a => ?_⟩
  exact shadow_magnitude_comparison ν m (S a) (Dν a) (Dm a) Cν Cm _
    (hνl a) (hνu a) (hml a) (hmu a) hl hu

end Singularity
