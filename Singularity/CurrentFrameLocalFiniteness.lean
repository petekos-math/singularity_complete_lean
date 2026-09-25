import Singularity.CurrentFrameLift
import Singularity.FrameEndpointContinuity

/-!
# Local finiteness of lifted currents

A fibre slice of a compact frame set K has Haar measure at most that of
(K K⁻¹) intersected with the stabilizer: choose one frame in the slice and
translate every other frame against it. This bound is uniform in the endpoints
and avoids any local boundedness assumption on the measurable section.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped MatrixGroups Pointwise

namespace Singularity

attribute [local instance] slTwo_polishSpace frameStabilizer_measurableMul frameStabilizer_measurableInv

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]

/-- The compact set of possible fibre displacements between two frames in K. -/
def compactFrameDisplacements (K : Set SL(2, ℝ)) : Set frameStabilizer :=
  {h | (h : SL(2, ℝ)) ∈ K * K⁻¹}

omit [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)] in
theorem isCompact_compactFrameDisplacements {K : Set SL(2, ℝ)} (hK : IsCompact K) :
    IsCompact (compactFrameDisplacements K) :=
  isClosed_frameStabilizer.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.mul hK.inv)

/-- Every fibre slice of a compact frame set satisfies the same Haar bound. -/
theorem compact_frame_fibre_measure_le (η : Measure frameStabilizer) [η.IsMulRightInvariant]
    {K : Set SL(2, ℝ)} (hK : IsCompact K) (p : BoundaryPair) :
    η {h | frameFromCoordinates (p, h) ∈ K} ≤ η (compactFrameDisplacements K) := by
  classical
  let S : Set frameStabilizer := {h | frameFromCoordinates (p, h) ∈ K}
  by_cases hs : S.Nonempty
  · obtain ⟨h₀, hh₀⟩ := hs
    have hsub : S ⊆ (fun h : frameStabilizer => h * h₀⁻¹) ⁻¹' compactFrameDisplacements K := by
      intro h hh
      change ((h : SL(2, ℝ)) * (h₀ : SL(2, ℝ))⁻¹) ∈ K * K⁻¹
      refine Set.mem_mul.mpr ⟨frameFromCoordinates (p, h), hh,
        (frameFromCoordinates (p, h₀))⁻¹, ?_, ?_⟩
      · simpa only [Set.mem_inv, inv_inv, S, Set.mem_ofPred_eq] using hh₀
      · simp [frameFromCoordinates, mul_inv_rev, mul_assoc]
    have hD := (isCompact_compactFrameDisplacements hK).isClosed.measurableSet
    exact (measure_mono hsub).trans_eq
      ((measurePreserving_mul_right η h₀⁻¹).measure_preimage hD.nullMeasurableSet)
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
    change η S ≤ _
    rw [he, measure_empty]
    exact bot_le

/-- A quantitative bound on the lift of a compact frame set. -/
theorem currentFrameLift_compact_bound (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [SFinite η] [η.IsMulRightInvariant] {K : Set SL(2, ℝ)} (hK : IsCompact K) :
    currentFrameLift J η K ≤
      η (compactFrameDisplacements K) * J (inverseFrameEndpoints '' K) := by
  have hU := (hK.image continuous_inverseFrameEndpoints).isClosed.measurableSet
  rw [currentFrameLift, Measure.map_apply measurable_frameFromCoordinates hK.isClosed.measurableSet,
    Measure.prod_apply (measurable_frameFromCoordinates hK.isClosed.measurableSet)]
  calc
    _ ≤ ∫⁻ p, (inverseFrameEndpoints '' K).indicator
        (fun _ => η (compactFrameDisplacements K)) p ∂J := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ inverseFrameEndpoints '' K
      · rw [Set.indicator_of_mem hp]
        exact compact_frame_fibre_measure_le η hK p
      · rw [Set.indicator_of_notMem hp]
        have he : {h : frameStabilizer | frameFromCoordinates (p, h) ∈ K} = ∅ := by
          apply Set.eq_empty_of_forall_notMem
          intro h hh
          exact hp ⟨frameFromCoordinates (p, h), hh, frameFromCoordinates_endpoints (p, h)⟩
        change η {h : frameStabilizer | frameFromCoordinates (p, h) ∈ K} ≤ 0
        rw [he, measure_empty]
    _ = _ := lintegral_indicator_const hU _

/-- A locally finite current lifted by locally finite fibre Haar measure is finite on compacts. -/
theorem currentFrameLift_finiteOnCompacts (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [IsLocallyFiniteMeasure J] [SFinite η] [IsLocallyFiniteMeasure η] [η.IsMulRightInvariant] :
    IsFiniteMeasureOnCompacts (currentFrameLift J η) := by
  constructor
  intro K hK
  exact (currentFrameLift_compact_bound J η hK).trans_lt
    (ENNReal.mul_lt_top (isCompact_compactFrameDisplacements hK).measure_lt_top
      (hK.image continuous_inverseFrameEndpoints).measure_lt_top)

/-- Local finiteness of the frame lift follows from local finiteness of the current and Haar fibre. -/
theorem currentFrameLift_locallyFinite (J : Measure BoundaryPair) (η : Measure frameStabilizer)
    [IsLocallyFiniteMeasure J] [SFinite η] [IsLocallyFiniteMeasure η] [η.IsMulRightInvariant] :
    IsLocallyFiniteMeasure (currentFrameLift J η) := by
  let := slTwo_locallyCompactSpace
  let := currentFrameLift_finiteOnCompacts J η
  infer_instance

end Singularity
