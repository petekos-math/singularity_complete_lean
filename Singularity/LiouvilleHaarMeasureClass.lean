import Singularity.HomogeneousMeasureClass
import Singularity.BoundaryActionMeasurable
import Singularity.LiouvilleInvariance
import Singularity.SLTwoHaar
import Singularity.DilationNorthSouth

/-!
# Haar endpoint maps and the concrete Liouville measure class

The explicit boundary-pair space is transitive and jointly measurable under
SL(2,ℝ). Its already constructed nonzero sigma-finite Liouville current is
invariant, so the homogeneous-space Fubini argument identifies its null sets
with those of the Haar endpoint map. This does not yet transfer quotient-flow
ergodicity to the lattice action.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure OnePoint
open scoped MatrixGroups

namespace Singularity

/-- Endpoints in the inverse-frame convention, suitable for the right-coset quotient. -/
def inverseFrameEndpoints (g : SL(2, ℝ)) : BoundaryPair := g⁻¹ • baseBoundaryPair

theorem measurable_inverseFrameEndpoints
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)] :
    Measurable inverseFrameEndpoints := by
  let := boundaryPair_measurableSMul
  exact measurable_inv.smul measurable_const

/-- Positive and negative diagonal times fix the vertical geodesic's endpoints. -/
theorem dilation_fixes_baseBoundaryPair (t : ℝ) : dilationMatrix t • baseBoundaryPair = baseBoundaryPair := by
  apply Subtype.ext
  change (dilationMatrix t • (∞ : OnePoint ℝ), dilationMatrix t • ((0 : ℝ) : OnePoint ℝ)) = _
  rw [compactBoundary_dilation_infty, compactBoundary_dilation_coe]
  simp [baseBoundaryPair]

/-- Left multiplication by the geodesic flow does not change inverse-frame endpoints. -/
theorem inverseFrameEndpoints_dilation (t : ℝ) (g : SL(2, ℝ)) :
    inverseFrameEndpoints (dilationMatrix t * g) = inverseFrameEndpoints g := by
  unfold inverseFrameEndpoints
  rw [mul_inv_rev, mul_smul, dilationMatrix_inv, dilation_fixes_baseBoundaryPair]

/-- Right multiplication changes inverse-frame endpoints by the inverse boundary action. -/
theorem inverseFrameEndpoints_mul (g h : SL(2, ℝ)) :
    inverseFrameEndpoints (g * h) = h⁻¹ • inverseFrameEndpoints g := by
  simp only [inverseFrameEndpoints, mul_inv_rev, mul_smul]

/-- Haar endpoint images and the explicit Liouville current have exactly the same null sets. -/
theorem inverseFrameEndpoints_measureClass
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν] :
    ν.map inverseFrameEndpoints ≪ compactLiouvilleCurrent ∧
      compactLiouvilleCurrent ≪ ν.map inverseFrameEndpoints := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := boundaryPair_pretransitive
  let := boundaryPair_measurableSMul
  let := compactLiouvilleCurrent_sigmaFinite
  let : NeZero compactLiouvilleCurrent := ⟨compactLiouvilleCurrent_ne_zero⟩
  let := compactLiouvilleCurrent_smulInvariant
  exact inverse_orbit_map_measureClass ν compactLiouvilleCurrent baseBoundaryPair

end Singularity
