import Singularity.CurrentFrameLocalFiniteness
import Singularity.FrameFiberHaar
import Singularity.HomogeneousMeasureClass

/-!
# The Liouville frame lift has Haar measure class

The lift is nonzero and sigma-finite, and right invariance follows from
Liouville invariance. A homogeneous-space Fubini argument then compares it
with Haar measure. This supplies the reference measure class for stable
endpoint charts without assuming a coordinate Jacobian formula.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups

namespace Singularity

/-- Nonzero sigma-finite right-invariant measures have the Haar measure class. -/
theorem rightInvariant_measureClass {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (ρ m : Measure G) [SFinite ρ] [NeZero ρ] [ρ.IsMulLeftInvariant]
    [SFinite m] [NeZero m] [m.IsMulRightInvariant] : m ≪ ρ ∧ ρ ≪ m := by
  let : NeZero ρ.inv := ⟨(Measure.map_ne_zero_iff measurable_inv.aemeasurable).mpr (NeZero.ne ρ)⟩
  let : NeZero m.inv := ⟨(Measure.map_ne_zero_iff measurable_inv.aemeasurable).mpr (NeZero.ne m)⟩
  have h := orbit_map_measureClass ρ.inv m.inv (1 : G)
  simp only [smul_eq_mul, mul_one] at h
  change (ρ.inv.map id ≪ m.inv) ∧ (m.inv ≪ ρ.inv.map id) at h
  rw [Measure.map_id] at h
  have h₁ := h.1.map measurable_inv
  have h₂ := h.2.map measurable_inv
  change ρ.inv.inv ≪ m.inv.inv at h₁
  change m.inv.inv ≪ ρ.inv.inv at h₂
  simpa only [Measure.inv_inv] using And.intro h₂ h₁

attribute [local instance] slTwo_polishSpace slTwo_locallyCompactSpace frameStabilizer_measurableMul
  frameStabilizer_measurableInv frameFiberHaar_sigmaFinite frameFiberHaar_isHaar
  frameFiberHaar_rightInvariant frameFiberHaar_locallyFinite compactLiouvilleCurrent_sigmaFinite

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]

/-- The actual lift of the Liouville current by the signed diagonal Haar fibre. -/
def liouvilleFrameMeasure : Measure SL(2, ℝ) :=
  currentFrameLift compactLiouvilleCurrent frameFiberHaar

theorem liouvilleFrameMeasure_sigmaFinite : SigmaFinite liouvilleFrameMeasure :=
  currentFrameLift_sigmaFinite _ _

theorem liouvilleFrameMeasure_ne_zero : liouvilleFrameMeasure ≠ 0 :=
  currentFrameLift_ne_zero _ _ compactLiouvilleCurrent_ne_zero

theorem liouvilleFrameMeasure_rightInvariant : liouvilleFrameMeasure.IsMulRightInvariant := by
  constructor
  intro g
  exact (currentFrameLift_right_invariant _ _ g
    ⟨measurable_const_smul _, compactLiouvilleCurrent_invariant _⟩).map_eq

theorem liouvilleFrameMeasure_locallyFinite : IsLocallyFiniteMeasure liouvilleFrameMeasure := by
  let := compactLiouvilleCurrent_locallyFinite
  exact currentFrameLift_locallyFinite _ _

/-- Haar and the explicit endpoint/fibre product lift detect exactly the same null sets. -/
theorem liouvilleFrameMeasure_measureClass (ρ : Measure SL(2, ℝ)) [IsHaarMeasure ρ] :
    liouvilleFrameMeasure ≪ ρ ∧ ρ ≪ liouvilleFrameMeasure := by
  let := liouvilleFrameMeasure_sigmaFinite
  let := liouvilleFrameMeasure_rightInvariant
  let : NeZero liouvilleFrameMeasure := ⟨liouvilleFrameMeasure_ne_zero⟩
  exact rightInvariant_measureClass ρ liouvilleFrameMeasure

end Singularity
