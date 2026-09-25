import Singularity.FrameStabilizer

/-!
# Haar measure in the full frame fibre

Choose Haar measure on the closed signed diagonal stabilizer. Its nonzero,
sigma-finite and two-sided-invariance properties are proved from the concrete
stabilizer; they are not added as assumptions on the random walk.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups

namespace Singularity

attribute [local instance] frameStabilizer_locallyCompact frameStabilizer_polish
  frameStabilizer_measurableMul frameStabilizer_measurableInv

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]

/-- Haar measure on the full signed diagonal fibre. -/
def frameFiberHaar : Measure frameStabilizer := Measure.haar

theorem frameFiberHaar_isHaar : IsHaarMeasure frameFiberHaar := by
  unfold frameFiberHaar
  infer_instance

theorem frameFiberHaar_ne_zero : frameFiberHaar ≠ 0 := by
  let := frameFiberHaar_isHaar
  exact NeZero.ne _

theorem frameFiberHaar_sigmaFinite : SigmaFinite frameFiberHaar := by
  let := frameFiberHaar_isHaar
  infer_instance

theorem frameFiberHaar_locallyFinite : IsLocallyFiniteMeasure frameFiberHaar := by
  let := frameFiberHaar_isHaar
  infer_instance

theorem frameFiberHaar_leftInvariant : frameFiberHaar.IsMulLeftInvariant := by
  let := frameFiberHaar_isHaar
  infer_instance

theorem frameFiberHaar_rightInvariant : frameFiberHaar.IsMulRightInvariant := by
  let := frameFiberHaar_leftInvariant
  exact frameStabilizer_rightInvariant frameFiberHaar

end Singularity
