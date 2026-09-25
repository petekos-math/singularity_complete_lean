import Singularity.HittingConjugacy
import Singularity.WalkIsomorphism

/-!
# The hitting measure in normalized hyperbolic coordinates

The normalized law uses the actual support B⁻¹ s B and its transported weights.
All probability and generation hypotheses are derived, and nonamenability
supplies its spectral gap. Its hitting measure is exactly the B⁻¹-pushforward
of the original hitting measure.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- The inverse coordinate map intertwines the original and conjugated actions. -/
theorem conjugateSubgroup_inverse_hyperbolic_action (Γ : Subgroup SL(2, ℝ))
    (B : SL(2, ℝ)) (g : Γ) (z : ℍ) :
    B⁻¹ • (g • z) = (conjugateSubgroupEquiv Γ B).symm g • (B⁻¹ • z) := by
  apply MulAction.injective B
  dsimp only
  rw [smul_inv_smul, conjugateSubgroup_hyperbolic_action,
    MulEquiv.apply_symm_apply, smul_inv_smul]

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (B : SL(2, ℝ)) [MeasurableSpace (conjugateSubgroup Γ B)]
  [MeasurableSingletonClass (conjugateSubgroup Γ B)] [MeasurableMul (conjugateSubgroup Γ B)]
  (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 < μ g)
  (hm : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hNA : ¬HasInvariantMean Γ)

/-- The actual hitting measure of the normalized walk, with all walk data transported. -/
def normalizedGeometricHittingMeasure (z : ℍ) : Measure (OnePoint ℝ) :=
  letI := conjugateSubgroup_discrete Γ B
  let e := (conjugateSubgroupEquiv Γ B).symm
  geometricHittingMeasure (conjugateSubgroup Γ B) (s.map e.toEmbedding) (μ ∘ e.symm)
    (mappedSupport_positive e s μ hμ) (mappedSupport_mass e s μ hm)
    (mappedSupport_generates e s hgen) (mappedSupport_spectralGap e s μ hμ hm hgen hNA) (B⁻¹ • z)

/-- Normalization transports the genuine hitting law by the inverse coordinate matrix. -/
theorem normalizedGeometricHittingMeasure_eq (z : ℍ) :
    normalizedGeometricHittingMeasure Γ B s μ hμ hm hgen hNA z =
      Measure.map (fun p : OnePoint ℝ => B⁻¹ • p)
        (geometricHittingMeasure Γ s μ hμ hm hgen
          (rightMarkov_nonamenable_spectral_gap s μ hμ hm hgen hNA) z) := by
  let := conjugateSubgroup_discrete Γ B
  let e := (conjugateSubgroupEquiv Γ B).symm
  exact geometricHittingMeasure_transport Γ (conjugateSubgroup Γ B)
    s (s.map e.toEmbedding) (mappedSupportEquiv e s) μ (μ ∘ e.symm)
    hμ (mappedSupport_positive e s μ hμ) hm (mappedSupport_mass e s μ hm)
    hgen (mappedSupport_generates e s hgen)
    (rightMarkov_nonamenable_spectral_gap s μ hμ hm hgen hNA)
    (mappedSupport_spectralGap e s μ hμ hm hgen hNA)
    (fun g => by change μ (e.symm (e g)) = μ g; rw [e.symm_apply_apply])
    e.toMonoidHom (fun _ => rfl) B⁻¹ (conjugateSubgroup_inverse_hyperbolic_action Γ B) z

/-- The original and normalized walks have equivalent visual-singularity conclusions. -/
theorem normalizedGeometricHittingMeasure_singularity_iff (z : ℍ) :
    normalizedGeometricHittingMeasure Γ B s μ hμ hm hgen hNA z ⟂ₘ compactPoissonMeasure (B⁻¹ • z) ↔
      geometricHittingMeasure Γ s μ hμ hm hgen
        (rightMarkov_nonamenable_spectral_gap s μ hμ hm hgen hNA) z ⟂ₘ compactPoissonMeasure z := by
  rw [normalizedGeometricHittingMeasure_eq]
  exact compactBoundary_visual_singularity_conjugacy B⁻¹ _ z

end Singularity
