import Singularity.FrameEndpointContinuity
import Singularity.ShearContraction

/-!
# Joint dependence on a frame and a finite boundary coordinate

A real coordinate is the image of zero under an upper shear. Multiplication
of frames and continuity of the zero-endpoint orbit map give joint continuity,
including when the image coordinate passes through infinity.
-/

noncomputable section
open scoped MatrixGroups

namespace Singularity

/-- The upper shear sends the boundary origin to its real parameter. -/
theorem upperShearMatrix_smul_boundary_zero (x : ℝ) :
    upperShearMatrix x • ((0 : ℝ) : OnePoint ℝ) = (x : OnePoint ℝ) := by
  rw [compactBoundary_smul_finite _ _ (by simp [upperShearMatrix])]
  simp [realBoundaryMobius, upperShearMatrix]

/-- Frame action is jointly continuous in the matrix and finite input
coordinate, even at a matrix/input pair whose image is infinity. -/
theorem continuous_frame_real_boundary_action :
    Continuous (fun p : SL(2, ℝ) × ℝ => p.1 • (p.2 : OnePoint ℝ)) := by
  have h := (continuous_compactBoundary_orbit ((0 : ℝ) : OnePoint ℝ)).comp
    (continuous_fst.mul (continuous_upperShearMatrix.comp continuous_snd))
  simpa only [Function.comp_def, Pi.mul_apply, mul_smul, upperShearMatrix_smul_boundary_zero] using h

end Singularity
