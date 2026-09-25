import Singularity.FiniteLastExitVertex
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Changing the starting vertex in last-exit expectations

The finite last-exit laws have an exact Martin density. Their realizations on
the original walk space therefore satisfy the corresponding integral identity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ] [Countable Γ]

/-- Integrating any real test function of the last-exit vertex is a finite sum. -/
theorem integral_finiteLastExitVertex (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Finset Γ) (x : Γ) (hx : x ∈ A) (f : A → ℝ) :
    (∫ ω, f (finiteLastExitVertex s A x hx ω) ∂infiniteWalkLaw s μ hμ hmass) =
      ∑ a : A, (finiteLastExitLaw s μ hμ hmass hgap A x hx a).toReal * f a := by
  rw [← integral_map_of_stronglyMeasurable (measurable_finiteLastExitVertex s A x hx)
    (measurable_of_countable f).stronglyMeasurable,
    finiteLastExitVertex_law s μ hμ hmass hgap A x hx,
    integral_fintype (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  rfl

/-- Exact change-of-start identity on the actual infinite path space. -/
theorem finiteLastExitVertex_change_start (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Finset Γ) (o x : Γ) (ho : o ∈ A) (hx : x ∈ A) (f : Γ → ℝ) :
    (∫ ω, f (finiteLastExitVertex s A x hx ω)
      ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass) =
    ∫ ω, martinQuotient s μ o x (finiteLastExitVertex s A o ho ω) *
      f (finiteLastExitVertex s A o ho ω)
      ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass := by
  rw [integral_finiteLastExitVertex s μ _ hmass hgap A x hx (fun a => f a),
    integral_finiteLastExitVertex s μ _ hmass hgap A o ho
      (fun a => martinQuotient s μ o x a * f a)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [finiteLastExitLaw_martin_density s μ hpos hmass hgen hgap A o x ho hx a,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (martinQuotient_pos s μ hpos hgen hgap o x a).le]
  ring

end Singularity
