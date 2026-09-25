import Singularity.LastExitConvergence
import Singularity.HittingBasepoint
import Singularity.CompactMartinMap

/-!
# Geometric and Martin limits along actual last-exit vertices

Finite-set exhaustion transfers the actual orbit limit to last-exit vertices.
The established arbitrary-approach Martin convergence then identifies the
almost-sure limits of their likelihood factors.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

/-- Last-exit vertices from any start converge to that start's actual boundary limit. -/
theorem geometricLastExitVertex_ae_tendsto (A : ℕ → Finset Γ) (x : Γ)
    (hx : ∀ n, x ∈ A n) (hexhaust : ∀ g, ∀ᶠ n in atTop, g ∈ A n) (z : ℍ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (finiteLastExitVertex s (A n) x (hx n) ω • z))
        atTop (𝓝 (compactBoundaryEmbedding
          (x • geometricBoundaryMap Γ s μ hpos hmass hgen hgap z ω))) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  exact finiteLastExitVertex_ae_tendsto s μ (fun g hg => (hpos g hg).le) hmass hgap A x hx
    hexhaust (fun g => hyperbolicCompactEmbedding (g • z)) _
    (geometricBoundaryMap_start_tendsto Γ s μ hpos hmass hgen hgap z x)

variable [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

/-- The finite likelihood factors converge to the constructed compact Martin kernel
at the actual hitting point. -/
theorem lastExitMartinQuotient_ae_tendsto (A : ℕ → Finset Γ)
    (hA : ∀ n, 1 ∈ A n) (hexhaust : ∀ g, ∀ᶠ n in atTop, g ∈ A n) (x : Γ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => martinQuotient s μ 1 x (finiteLastExitVertex s (A n) 1 (hA n) ω))
        atTop (𝓝 ((compactMartinPoint Γ s μ hpos hgen hgap horbit
          (geometricBoundaryMap Γ s μ hpos hmass hgen hgap UpperHalfPlane.I ω)).val x)) := by
  filter_upwards [geometricLastExitVertex_ae_tendsto Γ s μ hpos hmass hgen hgap A 1 hA
    hexhaust UpperHalfPlane.I] with ω hω
  simp only [one_smul] at hω
  exact compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit _
    (fun n => finiteLastExitVertex s (A n) 1 (hA n) ω) hω x

end Singularity
