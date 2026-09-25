import Singularity.IndependentShift
import Singularity.WalkBoundaryLaw

/-!
# Ergodicity of a random-walk boundary law

Ergodicity here means the zero–one property for almost group-invariant sets.
The hitting measure need not itself be invariant under the group action.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

omit [MeasurableSingletonClass Γ] in
/-- The one-sided shift on the actual jump space has the zero–one property. -/
theorem infiniteWalkLaw_shift_zero_one (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    {E : Set (ℕ → s)} (hE : MeasurableSet E)
    (hinv : (fun (ω : ℕ → s) i => ω (i + 1)) ⁻¹' E =ᵐ[infiniteWalkLaw s μ hμ hmass] E) :
    infiniteWalkLaw s μ hμ hmass E = 0 ∨ infiniteWalkLaw s μ hμ hmass E = 1 := by
  apply independent_shift_event_zero_one _ (infiniteWalkLaw_independent s μ hμ hmass) hE
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : MeasurePreserving (fun (ω : ℕ → s) i => ω (i + n))
        (infiniteWalkLaw s μ hμ hmass) (infiniteWalkLaw s μ hμ hmass) :=
      ⟨by fun_prop, infiniteWalkLaw_shift s μ hμ hmass n⟩
    filter_upwards [hp.quasiMeasurePreserving.ae hinv, ih] with ω hω hi
    apply propext
    change (fun i => ω (i + (n + 1))) ∈ E ↔ ω ∈ E
    have h1 : (fun i => ω (i + (n + 1))) = (fun i => ω ((i + 1) + n)) := by
      funext i
      congr 1
      omega
    rw [h1]
    exact (iff_of_eq hω).trans (iff_of_eq hi)

variable [Group Γ] {B : Type*} [MeasurableSpace B] [MulAction Γ B]

omit [MeasurableSingletonClass Γ] in
/-- Every almost group-invariant measurable boundary event has hitting probability zero or one. -/
theorem walkBoundaryLaw_invariant_zero_one (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (b : (ℕ → s) → B) (hb : Measurable b)
    (hstep : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      b ω = (ω 0 : Γ) • b (fun n => ω (n + 1)))
    {E : Set B} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E =ᵐ[walkBoundaryLaw s μ hμ hmass b] E) :
    walkBoundaryLaw s μ hμ hmass b E = 0 ∨ walkBoundaryLaw s μ hμ hmass b E = 1 := by
  have hall : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      ∀ g : s, (g : Γ) • b ω ∈ E ↔ b ω ∈ E :=
    ae_all_iff.mpr (fun g => ae_of_ae_map hb.aemeasurable (hinv g).mem_iff)
  have hp : MeasurePreserving (fun (ω : ℕ → s) i => ω (i + 1))
      (infiniteWalkLaw s μ hμ hmass) (infiniteWalkLaw s μ hμ hmass) :=
    ⟨by fun_prop, infiniteWalkLaw_shift s μ hμ hmass 1⟩
  rw [walkBoundaryLaw, Measure.map_apply hb hE]
  apply infiniteWalkLaw_shift_zero_one s μ hμ hmass (hE.preimage hb)
  filter_upwards [hstep, hp.quasiMeasurePreserving.ae hall] with ω hω hi
  apply propext
  change b (fun i => ω (i + 1)) ∈ E ↔ b ω ∈ E
  rw [hω]
  exact (hi (ω 0)).symm

end Singularity
