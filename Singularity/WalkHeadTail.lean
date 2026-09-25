import Singularity.InfiniteWalkProcess
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Splitting the first jump from the infinite future

The head and the whole tail are independent, not merely each pair of
coordinates. This gives an exact product law and the first-step integration
formula used to construct stationary boundary distributions.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace Singularity

variable {Γ : Type*} [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

omit [MeasurableSingletonClass Γ] in
/-- The first jump is independent of the entire shifted sample. -/
theorem infiniteWalkLaw_head_tail_independent (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) :
    IndepFun (fun ω : ℕ → s => ω 0) (fun ω n => ω (n + 1))
      (infiniteWalkLaw s μ hμ hmass) := by
  apply IndepFun.indepFun_process (by fun_prop) (fun _ => by fun_prop)
  intro I
  have hdis : Disjoint ({0} : Finset ℕ) (I.image (fun n => n + 1)) := by simp
  have hi := (infiniteWalkLaw_independent s μ hμ hmass).indepFun_finset
    {0} (I.image (fun n => n + 1)) hdis (fun _ => by fun_prop)
  exact hi.comp (measurable_pi_apply ⟨0, by simp⟩)
    (measurable_pi_lambda _ (fun (i : I) => measurable_pi_apply
      ⟨i.val + 1, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩))

omit [MeasurableSingletonClass Γ] in
/-- The joint head-tail distribution is the product of the jump and path laws. -/
theorem infiniteWalkLaw_head_tail (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) :
    Measure.map (fun ω : ℕ → s => (ω 0, fun n => ω (n + 1)))
      (infiniteWalkLaw s μ hμ hmass) =
      (supportJumpLaw s μ hμ hmass).toMeasure.prod (infiniteWalkLaw s μ hμ hmass) := by
  rw [(infiniteWalkLaw_head_tail_independent s μ hμ hmass).map_prod_eq_prod_map_map
    (by exact (by fun_prop : Measurable (fun ω : ℕ → s => ω 0)).aemeasurable)
    (by exact (by fun_prop : Measurable (fun ω : ℕ → s => fun n => ω (n + 1))).aemeasurable), infiniteWalkLaw_coordinate, infiniteWalkLaw_shift]

/-- First-step integration with an arbitrary measurable nonnegative observable. -/
theorem infiniteWalkLaw_lintegral_head_tail (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (f : s × (ℕ → s) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (ω 0, fun n => ω (n + 1)) ∂infiniteWalkLaw s μ hμ hmass) =
      ∑ g : s, ENNReal.ofReal (μ g) *
        ∫⁻ ω, f (g, ω) ∂infiniteWalkLaw s μ hμ hmass := by
  rw [← lintegral_map hf (by fun_prop), infiniteWalkLaw_head_tail,
    lintegral_prod _ hf.aemeasurable, lintegral_fintype]
  apply Finset.sum_congr rfl
  intro g _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton g), supportJumpLaw_apply,
    mul_comm]

end Singularity
