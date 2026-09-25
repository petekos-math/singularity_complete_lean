import Singularity.CocompactLiouvilleErgodicity
import Singularity.GeometricHittingErgodicity
import Singularity.ErgodicMeasureFactor

/-!
# Ergodicity of the visual measure class and equivalence with a nonsingular hitting law

Projection to one endpoint transfers the proved cocompact Liouville ergodicity
to the visual measure class. Applying the null-set saturation argument in both
directions shows that a nonsingular hitting law is equivalent to visual measure.
This does not assert upper or lower uniform bounds for its density.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- The first marginal of the distinct-pair reference measure is its prescribed first probability. -/
theorem boundaryPairMeasure_first_marginal (μ ν : Measure (OnePoint ℝ))
    [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    Measure.map (fun p : BoundaryPair => p.val.1) (boundaryPairMeasure μ ν) = μ := by
  change Measure.map (Prod.fst ∘ Subtype.val) _ = _
  rw [← Measure.map_map measurable_fst measurable_subtype_coe,
    boundaryPairMeasure_map_eq, Measure.map_fst_prod, measure_univ, one_smul]

/-- The first marginal of Liouville current has the visual null sets, despite its infinite mass. -/
theorem compactLiouvilleCurrent_first_measureClass (z : ℍ) :
    (Measure.map (fun p : BoundaryPair => p.val.1) compactLiouvilleCurrent ≪ compactPoissonMeasure z) ∧
    (compactPoissonMeasure z ≪ Measure.map (fun p : BoundaryPair => p.val.1) compactLiouvilleCurrent) := by
  have := compactPoissonMeasure_probability UpperHalfPlane.I
  have := compactPoissonMeasure_nullSingleton UpperHalfPlane.I
  have h := boundaryPairCurrent_measureClass
    (compactPoissonMeasure UpperHalfPlane.I) (compactPoissonMeasure UpperHalfPlane.I)
    liouvilleBoundaryKernel continuous_liouvilleBoundaryKernel.measurable liouvilleBoundaryKernel_pos
  have hf : Measurable (fun p : BoundaryPair => p.val.1) := measurable_fst.comp measurable_subtype_coe
  have h1 := h.1.map hf
  have h2 := h.2.map hf
  rw [boundaryPairMeasure_first_marginal] at h1 h2
  exact ⟨h1.trans (compactPoissonMeasure_absolutelyContinuous _ _),
    (compactPoissonMeasure_absolutelyContinuous _ _).trans h2⟩

/-- Visual measure has the zero–one property for a discrete cocompact Fuchsian action. -/
theorem compactPoissonMeasure_invariant_zero_one_cocompact
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] (z : ℍ)
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' E =ᵐ[compactPoissonMeasure z] E) :
    compactPoissonMeasure z E = 0 ∨ compactPoissonMeasure z E = 1 := by
  have := compactLiouvilleCurrent_ergodic Γ
  have := compactPoissonMeasure_probability z
  exact invariant_zero_one_of_ergodic_factor (G := Γ) compactLiouvilleCurrent
    (compactPoissonMeasure z) (fun p : BoundaryPair => p.val.1)
    (measurable_fst.comp measurable_subtype_coe)
    (compactLiouvilleCurrent_first_measureClass z) (fun _ _ => rfl) hE hinv

/-- In the cocompact case a nonsingular hitting measure and visual measure have exactly the same null sets. -/
theorem geometricHittingMeasure_equivalent_of_not_singular_cocompact
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)
    (hns : ¬ geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z) :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪ compactPoissonMeasure z ∧
      compactPoissonMeasure z ≪ geometricHittingMeasure Γ s μ hpos hmass hgen hgap z := by
  refine ⟨geometricHittingMeasure_absolutelyContinuous_of_not_singular
    Γ s μ hpos hmass hgen hgap z hns, ?_⟩
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have := compactPoissonMeasure_probability z
  exact absolutelyContinuous_of_invariant_zero_one (G := Γ) _ _
    (fun g => (geometricHittingMeasure_translate_equivalent Γ s μ hpos hmass hgen hgap z g).1)
    (fun _ hE hinv => compactPoissonMeasure_invariant_zero_one_cocompact Γ z hE hinv)
    (fun h => hns h.symm)

end Singularity
