import Singularity.FiniteIndependentConditioning
import Singularity.WalkPrefixFiltration

/-!
# Conditional averaging over the independent infinite future

The conditional expectation given the first n increments is obtained by
holding those increments fixed and integrating a fresh infinite tail.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace Singularity

/-- Exact conditional averaging at deterministic time n. -/
theorem infiniteWalkLaw_condExp_prefix_tail
    {Γ : Type*} [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ)
    (f : (Fin n → s) → (ℕ → s) → ℝ)
    (hf : ∀ w, Measurable (f w))
    (hint : ∀ w, Integrable (f w) (infiniteWalkLaw s μ hμ hmass)) :
    (infiniteWalkLaw s μ hμ hmass)[
      fun ω => f (fun i => ω i.val) (fun k => ω (k + n)) | walkPrefixFiltration s n] =ᵐ[
        infiniteWalkLaw s μ hμ hmass]
      fun ω => ∫ η, f (fun i => ω i.val) η ∂infiniteWalkLaw s μ hμ hmass := by
  let P := infiniteWalkLaw s μ hμ hmass
  have hshift : MeasurePreserving (fun (ω : ℕ → s) k => ω (k + n)) P P :=
    ⟨by fun_prop, infiniteWalkLaw_shift s μ hμ hmass n⟩
  have hind : IndepFun (fun (ω : ℕ → s) (i : Fin n) => ω i.val)
      (fun (ω : ℕ → s) k => ω (k + n)) P := by
    have h := (infiniteWalkLaw_prefix_tail_independent s μ hμ hmass n).comp
      (measurable_of_countable (walkWordEquivFin s n)) measurable_id
    simpa only [Function.comp_def, walkPrefix, Equiv.apply_symm_apply, id_eq] using h
  rw [walkPrefixFiltration_eq_comap]
  have hc := condExp_finite_independent P
    (fun (ω : ℕ → s) (i : Fin n) => ω i.val)
    (fun (ω : ℕ → s) k => ω (k + n)) (by fun_prop) (by fun_prop) hind f hf
    (fun w => hshift.integrable_comp_of_integrable (hint w))
  filter_upwards [hc] with ω hω
  rw [hω, ← integral_map hshift.measurable.aemeasurable (hf _).aestronglyMeasurable,
    hshift.map_eq]

end Singularity
