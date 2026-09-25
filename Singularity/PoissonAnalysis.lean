import Singularity.PoissonDecay
import Singularity.AnalysisKernel

/-!
# Analysis operators from Poisson-dominated logarithmic densities

Pointwise Poisson domination now supplies both integrability and exponential
decay. The input still requires the geometric domination, measurability,
nonnegativity, and the subprobability mass bound.
-/

noncomputable section
open MeasureTheory

namespace Singularity

variable {J : Type*} [Fintype J] {τ : ℝ} (hτ : 0 < τ)
  (k : J → ℝ → ℝ) (x y B : J → ℝ)
  (hy : ∀ j, 0 < y j) (hB : ∀ j, 0 ≤ B j)
  (hkm : ∀ j, AEStronglyMeasurable (k j)) (hk0 : ∀ j t, 0 ≤ k j t)
  (hmass : ∀ j, ∫ t, k j t ≤ 1)
  (hdom : ∀ j t, k j t ≤ B j * logPoissonProfile (x j) (y j) t)

/-- Construct the actual lattice density family from Poisson domination alone,
without a separate integrability or exponential-decay hypothesis. -/
def poissonDominatedDensityFamily : DensityFamily ℝ (ℤ × J) volume :=
  translatedDensityFamily hτ k (fun j => B j * poissonEnvelopeConstant (x j) (y j))
    (fun j => mul_nonneg (hB j) (poissonEnvelopeConstant_pos (x j) (hy j)).le)
    hk0 (fun j => poisson_dominated_integrable (x j) (hy j) (k j) (hkm j) (hk0 j) (hdom j))
    hmass (fun j t => poisson_dominated_decay (x j) (hy j) (hB j) (k j) (hdom j) t)

/-- The constructed analysis map uses exactly the prescribed translated densities. -/
theorem poissonDominated_analysis_apply (f : RealLineL2) (n : ℤ) (j : J) :
    (poissonDominatedDensityFamily hτ k x y B hy hB hkm hk0 hmass hdom).analysis f (n, j) =
      ∫ t, (k j (t - (n : ℝ) * τ) : ℂ) * f t := by
  unfold poissonDominatedDensityFamily
  exact translated_analysis_apply _ _ _ _ _ _ _ _ f n j

/-- The resulting bounded analysis operator has a nonzero kernel. -/
theorem poissonDominated_analysis_has_kernel :
    ∃ φ : RealLineL2, φ ≠ 0 ∧
      (poissonDominatedDensityFamily hτ k x y B hy hB hkm hk0 hmass hdom).analysis φ = 0 := by
  unfold poissonDominatedDensityFamily
  exact translated_analysis_has_kernel _ _ _ _ _ _ _ _

end Singularity
