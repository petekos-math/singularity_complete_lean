import Singularity.WalkKernel
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Actual finite-time probability laws

The product weights on jump words define a probability mass function. Its
pushforward by the endpoint map gives precisely the transition kernel used
in the Green-series identification. InfiniteWalkLaw.lean later constructs
the infinite-time path space with these finite-dimensional distributions.
-/

noncomputable section
open scoped BigOperators Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The probability law of all length-n jump words. -/
def finiteWalkLaw (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) :
    PMF (WalkWord s n) :=
  PMF.ofFintype (fun w => ENNReal.ofReal (walkWeight s μ n w)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => walkWeight_nonneg s μ hμ n w),
      walkWeight_mass s μ hmass n, ENNReal.ofReal_one])

omit [Group Γ] in
/-- Its weight at a given word is the product of that word's jump weights. -/
theorem finiteWalkLaw_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (n : ℕ) (w : WalkWord s n) :
    finiteWalkLaw s μ hμ hmass n w = ENNReal.ofReal (walkWeight s μ n w) := rfl

/-- The distribution of the endpoint of the finite random walk. -/
def finiteEndpointLaw (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) (x : Γ) : PMF Γ :=
  (finiteWalkLaw s μ hμ hmass n).map (walkEndpoint s n x)

/-- Transition weights are the probabilities under the actual endpoint law. -/
theorem finiteEndpointLaw_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) (x y : Γ) :
    finiteEndpointLaw s μ hμ hmass n x y = ENNReal.ofReal (transitionWeight s μ n x y) := by
  rw [finiteEndpointLaw, PMF.map_apply, tsum_fintype, transitionWeight]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro w _
    rw [finiteWalkLaw_apply]
    simp only [eq_comm]
    split_ifs <;> simp
  · intro w _
    split_ifs
    · exact walkWeight_nonneg s μ hμ n w
    · exact le_rfl

/-- The real-valued probability matches the matrix coefficient notation. -/
theorem finiteEndpointLaw_toReal (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) (x y : Γ) :
    (finiteEndpointLaw s μ hμ hmass n x y).toReal = transitionWeight s μ n x y := by
  rw [finiteEndpointLaw_apply, ENNReal.toReal_ofReal (transitionWeight_nonneg s μ hμ n x y)]

/-- The Green path sum is the sum of the actual n-step endpoint probabilities. -/
theorem walkGreen_eq_sum_endpoint_probabilities (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (x y : Γ) :
    walkGreen s μ x y = ∑' n : ℕ, (finiteEndpointLaw s μ hμ hmass n x y).toReal := by
  simp only [finiteEndpointLaw_toReal, walkGreen]

end Singularity
