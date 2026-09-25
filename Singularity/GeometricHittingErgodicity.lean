import Singularity.WalkBoundaryErgodicity
import Singularity.ErgodicMeasureDichotomy
import Singularity.GeometricHittingMeasure

/-!
# Ergodicity and the absolute-continuity dichotomy for the geometric hitting law

These results concern the constructed hitting measure. Its first-step cocycle
is deduced from convergence of the orbit in the compactification. Nonsingularity
against visual measure then implies absolute continuity; no bounds on the
resulting density or Green-function comparison are asserted here.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- Visual measures at any two interior basepoints have the same null sets. -/
theorem compactPoissonMeasure_absolutelyContinuous (z w : ℍ) :
    compactPoissonMeasure z ≪ compactPoissonMeasure w := by
  have hz := (halfPlanePoissonMeasure_measureClass z.re z.im_pos).1
  have hw := (halfPlanePoissonMeasure_measureClass w.re w.im_pos).2
  exact (hz.trans hw).map OnePoint.continuous_coe.measurable

/-- The visual measure class is preserved by every real determinant-one matrix. -/
theorem compactPoissonMeasure_quasiInvariant (z : ℍ) (g : SL(2, ℝ)) :
    Measure.map (fun ξ : OnePoint ℝ => g • ξ) (compactPoissonMeasure z) ≪
      compactPoissonMeasure z := by
  rw [compactPoissonMeasure_covariance]
  exact compactPoissonMeasure_absolutelyContinuous _ _

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ)
  (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)

/-- The actual real-projective boundary limit obeys the first-step cocycle almost surely. -/
theorem geometricBoundaryMap_first_step :
    let b := geometricBoundaryMap Γ s μ hpos hmass hgen hgap z
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      b ω = (ω 0 : Γ) • b (fun n => ω (n + 1)) := by
  let b := geometricBoundaryMap Γ s μ hpos hmass hgen hgap z
  have hc := walkBoundaryLimit_first_step s μ (fun g hg => (hpos g hg).le) hmass
    (fun g : Γ => hyperbolicCompactEmbedding (g • z)) (compactOrbit_equivariant Γ z)
    (fun ω => compactBoundaryEmbedding (b ω))
    (geometricBoundaryMap_tendsto Γ s μ hpos hmass hgen hgap z)
  filter_upwards [hc] with ω hω
  apply compactBoundaryEmbedding_injective
  exact hω.trans (compactBoundaryEmbedding_smul ((ω 0 : Γ) : SL(2, ℝ)) _).symm

/-- Almost group-invariant events have hitting probability zero or one. -/
theorem geometricHittingMeasure_invariant_zero_one
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' E =ᵐ[
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z] E) :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z E = 0 ∨
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z E = 1 :=
  walkBoundaryLaw_invariant_zero_one s μ (fun g hg => (hpos g hg).le) hmass _
    (measurable_geometricBoundaryMap Γ s μ hpos hmass hgen hgap z)
    (geometricBoundaryMap_first_step Γ s μ hpos hmass hgen hgap z) hE hinv

/-- Nonsingularity forces absolute continuity of the actual hitting law against visual measure. -/
theorem geometricHittingMeasure_absolutelyContinuous_of_not_singular
    (hns : ¬ geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z) :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪ compactPoissonMeasure z := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact absolutelyContinuous_of_invariant_zero_one (G := Γ) _ _
    (fun g => compactPoissonMeasure_quasiInvariant z (g : SL(2, ℝ)))
    (fun _ hE hinv => geometricHittingMeasure_invariant_zero_one
      Γ s μ hpos hmass hgen hgap z hE hinv) hns

end Singularity
