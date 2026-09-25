import Singularity.ConjugateSubgroup
import Singularity.BoundaryMeasureClasses

/-!
# Singularity under a change of hyperbolic coordinates

The compact boundary action is a measurable embedding, and visual measures
transform covariantly. Thus conjugating coordinates preserves and reflects the
singularity conclusion, including any atoms at infinity.
-/

noncomputable section
open MeasureTheory OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- Every real projective SL action is a measurable embedding on the compact boundary. -/
theorem measurableEmbedding_compactBoundary_smul (B : SL(2, ℝ)) :
    MeasurableEmbedding (fun p : OnePoint ℝ => B • p) :=
  ((continuous_const_smul B).isClosedEmbedding (MulAction.injective B)).measurableEmbedding

/-- The visual-singularity conclusion is invariant under a hyperbolic change of coordinates. -/
theorem compactBoundary_visual_singularity_conjugacy (B : SL(2, ℝ))
    (ν : Measure (OnePoint ℝ)) (z : ℍ) :
    Measure.map (fun p : OnePoint ℝ => B • p) ν ⟂ₘ compactPoissonMeasure (B • z) ↔
      ν ⟂ₘ compactPoissonMeasure z := by
  rw [← compactPoissonMeasure_covariance]
  exact mutuallySingular_map_iff_of_embedding _ (measurableEmbedding_compactBoundary_smul B) _ _

end Singularity
