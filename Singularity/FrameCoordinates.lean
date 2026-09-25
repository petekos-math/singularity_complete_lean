import Singularity.BoundaryFrameSection
import Singularity.FrameStabilizer

/-!
# Measurable frame coordinates and the right-action cocycle

Every special-linear frame is uniquely its explicit endpoint section followed
on the left by a stabilizer element. In these coordinates right multiplication
acts on endpoints and translates the stabilizer coordinate. This includes both
central signs, so no passage to a projective quotient is implicit.
-/

noncomputable section
open MeasureTheory OnePoint
open scoped MatrixGroups

namespace Singularity

attribute [local instance] slTwo_polishSpace

/-- The stabilizer coordinate of a frame relative to the explicit section. -/
def frameFiberCoordinate (g : SL(2, ℝ)) : frameStabilizer :=
  ⟨g * boundaryFrameSection (inverseFrameEndpoints g), by
    change (g * boundaryFrameSection (inverseFrameEndpoints g)) • baseBoundaryPair = baseBoundaryPair
    rw [mul_smul, boundaryFrameSection_endpoints]
    exact smul_inv_smul g baseBoundaryPair⟩

/-- Reassemble a frame from its endpoints and full signed diagonal coordinate. -/
def frameFromCoordinates (q : BoundaryPair × frameStabilizer) : SL(2, ℝ) :=
  (q.2 : SL(2, ℝ)) * inverseBoundaryFrameSection q.1

/-- Left stabilizer multiplication preserves inverse-frame endpoints. -/
theorem inverseFrameEndpoints_stabilizer_mul (h : frameStabilizer) (g : SL(2, ℝ)) :
    inverseFrameEndpoints ((h : SL(2, ℝ)) * g) = inverseFrameEndpoints g := by
  have hh : ((h : SL(2, ℝ))⁻¹) • baseBoundaryPair = baseBoundaryPair := (h⁻¹).property
  simp only [inverseFrameEndpoints, mul_inv_rev, mul_smul, hh]

theorem frameFromCoordinates_endpoints (q : BoundaryPair × frameStabilizer) :
    inverseFrameEndpoints (frameFromCoordinates q) = q.1 := by
  rw [frameFromCoordinates, inverseFrameEndpoints_stabilizer_mul,
    inverseBoundaryFrameSection_endpoints]

/-- Decomposing and reassembling a frame returns the original matrix. -/
theorem frameFromCoordinates_inverse (g : SL(2, ℝ)) :
    frameFromCoordinates (inverseFrameEndpoints g, frameFiberCoordinate g) = g := by
  simp [frameFromCoordinates, frameFiberCoordinate, inverseBoundaryFrameSection, mul_assoc]

/-- Reassembling and then extracting the fibre returns the full original fibre coordinate. -/
theorem frameFiberCoordinate_from (q : BoundaryPair × frameStabilizer) :
    frameFiberCoordinate (frameFromCoordinates q) = q.2 := by
  apply Subtype.ext
  change frameFromCoordinates q * boundaryFrameSection (inverseFrameEndpoints (frameFromCoordinates q)) = _
  rw [frameFromCoordinates_endpoints]
  simp [frameFromCoordinates, inverseBoundaryFrameSection, mul_assoc]

/-- The global frame decomposition as a bijection. -/
def frameCoordinatesEquiv : SL(2, ℝ) ≃ BoundaryPair × frameStabilizer where
  toFun g := (inverseFrameEndpoints g, frameFiberCoordinate g)
  invFun := frameFromCoordinates
  left_inv := frameFromCoordinates_inverse
  right_inv q := Prod.ext (frameFromCoordinates_endpoints q) (frameFiberCoordinate_from q)

section Measurable
variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]

theorem measurable_frameFiberCoordinate : Measurable frameFiberCoordinate := by
  exact (measurable_id.mul (measurable_boundaryFrameSection.comp measurable_inverseFrameEndpoints)).subtype_mk

theorem measurable_frameFromCoordinates : Measurable frameFromCoordinates := by
  exact (measurable_subtype_coe.comp measurable_snd).mul
    (measurable_inverseBoundaryFrameSection.comp measurable_fst)

/-- The frame decomposition and its inverse are both measurable. -/
def frameCoordinatesMeasurableEquiv : SL(2, ℝ) ≃ᵐ BoundaryPair × frameStabilizer where
  toEquiv := frameCoordinatesEquiv
  measurable_toFun := measurable_inverseFrameEndpoints.prodMk measurable_frameFiberCoordinate
  measurable_invFun := measurable_frameFromCoordinates

end Measurable

/-- The fibre correction under right multiplication of the chosen section. -/
def frameRightCocycle (g : SL(2, ℝ)) (p : BoundaryPair) : frameStabilizer :=
  frameFiberCoordinate (inverseBoundaryFrameSection p * g)

/-- Exact section transformation under the right group action. -/
theorem inverseBoundaryFrameSection_mul (g : SL(2, ℝ)) (p : BoundaryPair) :
    inverseBoundaryFrameSection p * g =
      (frameRightCocycle g p : SL(2, ℝ)) * inverseBoundaryFrameSection (g⁻¹ • p) := by
  have h := frameFromCoordinates_inverse (inverseBoundaryFrameSection p * g)
  rw [inverseFrameEndpoints_mul, inverseBoundaryFrameSection_endpoints] at h
  exact h.symm

/-- Right multiplication has the claimed skew-product coordinate formula. -/
theorem frameFromCoordinates_mul (q : BoundaryPair × frameStabilizer) (g : SL(2, ℝ)) :
    frameFromCoordinates q * g =
      frameFromCoordinates (g⁻¹ • q.1, q.2 * frameRightCocycle g q.1) := by
  change (q.2 : SL(2, ℝ)) * inverseBoundaryFrameSection q.1 * g =
    ((q.2 : SL(2, ℝ)) * (frameRightCocycle g q.1 : SL(2, ℝ))) *
      inverseBoundaryFrameSection (g⁻¹ • q.1)
  rw [mul_assoc, inverseBoundaryFrameSection_mul, mul_assoc]

/-- Left stabilizer multiplication translates only the fibre. -/
theorem stabilizer_mul_frameFromCoordinates (h : frameStabilizer)
    (q : BoundaryPair × frameStabilizer) :
    (h : SL(2, ℝ)) * frameFromCoordinates q = frameFromCoordinates (q.1, h * q.2) := by
  simp only [frameFromCoordinates, Subgroup.coe_mul, mul_assoc]

/-- The right-action correction depends measurably on the endpoint pair. -/
theorem measurable_frameRightCocycle
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)] (g : SL(2, ℝ)) :
    Measurable (frameRightCocycle g) :=
  measurable_frameFiberCoordinate.comp (measurable_inverseBoundaryFrameSection.mul_const g)

end Singularity
