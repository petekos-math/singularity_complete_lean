import Singularity.FrameCoordinates
import Mathlib.MeasureTheory.Group.Prod

/-!
# Lifting a boundary current to frames

Integrate Haar measure in the signed diagonal fibre of the explicit frame
coordinates. The resulting measure is invariant under the geodesic flow;
invariance of the current under a lattice gives right lattice invariance of
the lift. Local finiteness and quotient finiteness are separate obligations.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped MatrixGroups

namespace Singularity

attribute [local instance] slTwo_polishSpace frameStabilizer_measurableMul frameStabilizer_measurableInv

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]

/-- Lift a current by the full stabilizer fibre measure. -/
def currentFrameLift (J : Measure BoundaryPair) (η : Measure frameStabilizer) : Measure SL(2, ℝ) :=
  (J.prod η).map frameFromCoordinates

/-- In frame coordinates the lifted measure is exactly the original product. -/
theorem currentFrameLift_coordinates (J : Measure BoundaryPair) (η : Measure frameStabilizer) :
    (currentFrameLift J η).map frameCoordinatesMeasurableEquiv = J.prod η := by
  change ((J.prod η).map frameCoordinatesMeasurableEquiv.symm).map frameCoordinatesMeasurableEquiv = _
  exact frameCoordinatesMeasurableEquiv.symm.map_symm_map

/-- Sigma-finiteness is preserved by the measurable frame equivalence. -/
theorem currentFrameLift_sigmaFinite (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [SigmaFinite J] [SigmaFinite η] : SigmaFinite (currentFrameLift J η) :=
  frameCoordinatesMeasurableEquiv.symm.sigmaFinite_map

/-- The endpoint image has the current's measure class, although fibre mass can be infinite. -/
theorem currentFrameLift_map_endpoints (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [SFinite η] : (currentFrameLift J η).map inverseFrameEndpoints = η univ • J := by
  rw [currentFrameLift, Measure.map_map measurable_inverseFrameEndpoints measurable_frameFromCoordinates]
  have he : inverseFrameEndpoints ∘ frameFromCoordinates = Prod.fst :=
    funext frameFromCoordinates_endpoints
  rw [he, Measure.map_fst_prod]

theorem currentFrameLift_endpoint_measureClass (J : Measure BoundaryPair)
    (η : Measure frameStabilizer) [SFinite η] [NeZero η] :
    (currentFrameLift J η).map inverseFrameEndpoints ≪ J ∧
      J ≪ (currentFrameLift J η).map inverseFrameEndpoints := by
  rw [currentFrameLift_map_endpoints]
  exact ⟨smul_absolutelyContinuous, absolutelyContinuous_smul (NeZero.ne _)⟩

/-- A nonzero current and nonzero fibre measure produce a nonzero lift. -/
theorem currentFrameLift_ne_zero (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [SFinite η] [NeZero η] (hJ : J ≠ 0) : currentFrameLift J η ≠ 0 := by
  intro h
  have ha := (currentFrameLift_endpoint_measureClass J η).2
  rw [h, Measure.map_zero] at ha
  exact hJ (absolutelyContinuous_zero_iff.mp ha)

/-- Every left fibre translation preserves the lift. -/
theorem currentFrameLift_left_invariant (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [SFinite J] [SFinite η] [η.IsMulLeftInvariant] (h : frameStabilizer) :
    MeasurePreserving (fun g : SL(2, ℝ) => (h : SL(2, ℝ)) * g)
      (currentFrameLift J η) (currentFrameLift J η) := by
  let S : BoundaryPair × frameStabilizer → BoundaryPair × frameStabilizer :=
    fun q => (q.1, h * q.2)
  have hS : MeasurePreserving S (J.prod η) (J.prod η) :=
    (MeasurePreserving.id J).skew_product (measurable_const.mul measurable_snd)
      (Eventually.of_forall fun _ => map_mul_left_eq_self η h)
  refine ⟨measurable_const_mul _, ?_⟩
  rw [currentFrameLift, Measure.map_map (measurable_const_mul _) measurable_frameFromCoordinates]
  have he : (fun g : SL(2, ℝ) => (h : SL(2, ℝ)) * g) ∘ frameFromCoordinates =
      frameFromCoordinates ∘ S := funext (stabilizer_mul_frameFromCoordinates h)
  rw [he, ← Measure.map_map measurable_frameFromCoordinates hS.measurable, hS.map_eq]

/-- Geodesic-flow invariance holds for every real time. -/
theorem currentFrameLift_dilation_invariant (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [SFinite J] [SFinite η] [η.IsMulLeftInvariant] (t : ℝ) :
    MeasurePreserving (fun g : SL(2, ℝ) => dilationMatrix t * g)
      (currentFrameLift J η) (currentFrameLift J η) :=
  currentFrameLift_left_invariant J η ⟨dilationMatrix t, dilationMatrix_mem_frameStabilizer t⟩

/-- Endpoint invariance becomes right frame invariance, via a measurable fibre translation. -/
theorem currentFrameLift_right_invariant (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [SFinite J] [SFinite η] [η.IsMulRightInvariant] (g : SL(2, ℝ))
    (hJ : MeasurePreserving (fun p : BoundaryPair => g⁻¹ • p) J J) :
    MeasurePreserving (fun x : SL(2, ℝ) => x * g) (currentFrameLift J η) (currentFrameLift J η) := by
  let S : BoundaryPair × frameStabilizer → BoundaryPair × frameStabilizer :=
    fun q => (g⁻¹ • q.1, q.2 * frameRightCocycle g q.1)
  have hS : MeasurePreserving S (J.prod η) (J.prod η) :=
    hJ.skew_product (measurable_snd.mul ((measurable_frameRightCocycle g).comp measurable_fst))
      (Eventually.of_forall fun p => map_mul_right_eq_self η (frameRightCocycle g p))
  refine ⟨measurable_mul_const _, ?_⟩
  rw [currentFrameLift, Measure.map_map (measurable_mul_const _) measurable_frameFromCoordinates]
  have he : (fun x : SL(2, ℝ) => x * g) ∘ frameFromCoordinates =
      frameFromCoordinates ∘ S := funext (fun q => frameFromCoordinates_mul q g)
  rw [he, ← Measure.map_map measurable_frameFromCoordinates hS.measurable, hS.map_eq]

/-- Comparison of currents passes to their frame lifts with a common fibre measure. -/
theorem currentFrameLift_absolutelyContinuous (J K : Measure BoundaryPair)
    (η : Measure frameStabilizer) [SFinite η] (h : J ≪ K) :
    currentFrameLift J η ≪ currentFrameLift K η :=
  (h.prod AbsolutelyContinuous.rfl).map measurable_frameFromCoordinates

/-- Comparison of lifts also detects comparison of their original endpoint currents. -/
theorem currentFrameLift_absolutelyContinuous_iff (J K : Measure BoundaryPair)
    (η : Measure frameStabilizer) [SFinite η] [NeZero η] :
    currentFrameLift J η ≪ currentFrameLift K η ↔ J ≪ K := by
  constructor
  · intro h
    exact (currentFrameLift_endpoint_measureClass J η).2.trans
      ((h.map measurable_inverseFrameEndpoints).trans (currentFrameLift_endpoint_measureClass K η).1)
  · exact currentFrameLift_absolutelyContinuous J K η

/-- The lift does not depend on which measurable endpoint section is chosen. -/
theorem currentFrameLift_section_independent (J : Measure BoundaryPair)
    (η : Measure frameStabilizer) [SFinite J] [SFinite η] [η.IsMulRightInvariant]
    (r : BoundaryPair → SL(2, ℝ)) (hr : Measurable r)
    (hend : ∀ p, inverseFrameEndpoints (r p) = p) :
    (J.prod η).map (fun q : BoundaryPair × frameStabilizer => (q.2 : SL(2, ℝ)) * r q.1) =
      currentFrameLift J η := by
  let S : BoundaryPair × frameStabilizer → BoundaryPair × frameStabilizer :=
    fun q => (q.1, q.2 * frameFiberCoordinate (r q.1))
  have hS : MeasurePreserving S (J.prod η) (J.prod η) :=
    (MeasurePreserving.id J).skew_product
      (measurable_snd.mul (measurable_frameFiberCoordinate.comp (hr.comp measurable_fst)))
      (Eventually.of_forall fun p => map_mul_right_eq_self η (frameFiberCoordinate (r p)))
  have he : (fun q : BoundaryPair × frameStabilizer => (q.2 : SL(2, ℝ)) * r q.1) =
      frameFromCoordinates ∘ S := by
    funext q
    have h := frameFromCoordinates_inverse (r q.1)
    rw [hend] at h
    change (frameFiberCoordinate (r q.1) : SL(2, ℝ)) * inverseBoundaryFrameSection q.1 = r q.1 at h
    change (q.2 : SL(2, ℝ)) * r q.1 =
      ((q.2 : SL(2, ℝ)) * (frameFiberCoordinate (r q.1) : SL(2, ℝ))) *
        inverseBoundaryFrameSection q.1
    rw [mul_assoc, h]
  rw [he, ← Measure.map_map measurable_frameFromCoordinates hS.measurable, hS.map_eq]
  rfl

/-- Right multiplication transports the lift according to the endpoint action,
without assuming invariance of the current. -/
theorem currentFrameLift_right_transport (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [SFinite J] [SFinite η] [η.IsMulRightInvariant] (g : SL(2, ℝ)) :
    (currentFrameLift J η).map (fun x : SL(2, ℝ) => x * g) =
      currentFrameLift (J.map (fun p : BoundaryPair => g⁻¹ • p)) η := by
  let T : BoundaryPair → BoundaryPair := fun p => g⁻¹ • p
  have hT : Measurable T := (continuous_const_smul g⁻¹).measurable
  let S : BoundaryPair × frameStabilizer → BoundaryPair × frameStabilizer :=
    fun q => (T q.1, q.2 * frameRightCocycle g q.1)
  have hS : MeasurePreserving S (J.prod η) ((J.map T).prod η) :=
    (hT.measurePreserving J).skew_product
      (measurable_snd.mul ((measurable_frameRightCocycle g).comp measurable_fst))
      (Eventually.of_forall fun p => map_mul_right_eq_self η (frameRightCocycle g p))
  rw [currentFrameLift, Measure.map_map (measurable_mul_const _) measurable_frameFromCoordinates]
  have he : (fun x : SL(2, ℝ) => x * g) ∘ frameFromCoordinates =
      frameFromCoordinates ∘ S := funext (fun q => frameFromCoordinates_mul q g)
  rw [he, ← Measure.map_map measurable_frameFromCoordinates hS.measurable, hS.map_eq]
  rfl

end Singularity
