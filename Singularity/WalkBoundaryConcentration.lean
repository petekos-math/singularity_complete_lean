import Singularity.WalkPrefixConditioning
import Singularity.WalkBoundaryTimeCocycle

/-!
# Concentration of translated hitting laws along sample paths

For a measurable boundary map with the first-step relation, the translated
boundary probability is exactly a finite-prefix conditional expectation.
Levy convergence therefore gives concentration on every measurable boundary
event along almost every path, without shadow or cocompactness assumptions.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
  (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (b : (ℕ → s) → B) (hb : Measurable b)
  (hstep : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
    b ω = (ω 0 : Γ) • b (fun k => ω (k + 1)))

include hb hstep

/-- The translated hitting probability is the conditional probability of the
boundary event given the observed finite prefix. -/
theorem walkBoundaryLaw_condExp_event {E : Set B} (hE : MeasurableSet E) (n : ℕ) :
    (infiniteWalkLaw s μ hμ hmass)[(b ⁻¹' E).indicator (fun _ => (1 : ℝ)) |
        walkPrefixFiltration s n] =ᵐ[infiniteWalkLaw s μ hμ hmass]
      fun ω => (walkBoundaryLaw s μ hμ hmass b
        ((fun ξ : B => walkPosition s 1 n ω • ξ) ⁻¹' E)).toReal := by
  let pos : (Fin n → s) → Γ := fun w => walkEndpoint s n 1 ((walkWordEquivFin s n).symm w)
  let f : (Fin n → s) → (ℕ → s) → ℝ := fun w =>
    ((fun η => pos w • b η) ⁻¹' E).indicator (fun _ => 1)
  have hf (w : Fin n → s) : Measurable (f w) :=
    measurable_const.indicator (hE.preimage ((measurable_const_smul _).comp hb))
  have hint (w : Fin n → s) : Integrable (f w) (infiniteWalkLaw s μ hμ hmass) :=
    (integrable_const 1).indicator (hE.preimage ((measurable_const_smul _).comp hb))
  have he : (b ⁻¹' E).indicator (fun _ => (1 : ℝ)) =ᵐ[infiniteWalkLaw s μ hμ hmass]
      fun ω => f (fun i => ω i.val) (fun k => ω (k + n)) := by
    filter_upwards [walkBoundaryMap_time_cocycle s μ hμ hmass b hstep n] with ω hω
    change (if b ω ∈ E then 1 else 0) =
      (if walkPosition s 1 n ω • b (fun k => ω (k + n)) ∈ E then 1 else 0)
    rw [hω]
  have hc := (condExp_congr_ae (m := walkPrefixFiltration s n) he).trans
    (infiniteWalkLaw_condExp_prefix_tail s μ hμ hmass n f hf hint)
  filter_upwards [hc] with ω hω
  rw [hω]
  change (∫ η, ((fun η => walkPosition s 1 n ω • b η) ⁻¹' E).indicator
    (fun _ => (1 : ℝ)) η ∂infiniteWalkLaw s μ hμ hmass) = _
  have hset : MeasurableSet ((fun η : ℕ → s => walkPosition s 1 n ω • b η) ⁻¹' E) :=
    hE.preimage ((measurable_const_smul (walkPosition s 1 n ω)).comp hb)
  rw [integral_indicator_const (1 : ℝ) hset]
  simp only [smul_eq_mul, mul_one, measureReal_def, walkBoundaryLaw,
    Measure.map_apply hb (hE.preimage (measurable_const_smul (walkPosition s 1 n ω)))]
  rfl

/-- Translated hitting probabilities converge to the boundary event indicator
along almost every path. This is measure-theoretic concentration, independent
of any geometric shadow theorem. -/
theorem walkBoundaryLaw_event_concentration {E : Set B} (hE : MeasurableSet E) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => (walkBoundaryLaw s μ hμ hmass b
        ((fun ξ : B => walkPosition s 1 n ω • ξ) ⁻¹' E)).toReal)
        atTop (𝓝 ((b ⁻¹' E).indicator (fun _ => (1 : ℝ)) ω)) := by
  have ht := infiniteWalkLaw_condExp_prefix_tendsto s μ hμ hmass
    ((b ⁻¹' E).indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator (hE.preimage hb))
    ((integrable_const 1).indicator (hE.preimage hb))
  have he := ae_all_iff.mpr (fun n => walkBoundaryLaw_condExp_event s μ hμ hmass b hb hstep hE n)
  filter_upwards [ht, he] with ω ht he
  simpa only [he] using ht

end Singularity
