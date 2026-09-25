import Singularity.BoundaryPairTransitivity
import Singularity.SLTwoHaar

/-!
# The diagonal frame stabilizer

The stabilizer of the ordered pair (infinity, zero) consists precisely of the
determinant-one diagonal matrices. It is a closed abelian subgroup, including
both signs. Its Haar measure is the fibre measure used to lift currents.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped MatrixGroups Topology

namespace Singularity

/-- The full stabilizer of the ordered vertical endpoints, including the central sign. -/
def frameStabilizer : Subgroup SL(2, ℝ) := MulAction.stabilizer SL(2, ℝ) baseBoundaryPair

/-- A determinant-one triangular matrix has a nonzero lower diagonal entry. -/
theorem slTwo_lowerRight_ne_zero_of_lowerLeft_zero (g : SL(2, ℝ)) (hc : g 1 0 = 0) :
    g 1 1 ≠ 0 := by
  have hd := g.property
  rw [Matrix.det_fin_two] at hd
  intro hd0
  simp [hc, hd0] at hd

/-- Fixing the two endpoints is exactly the diagonal condition. -/
theorem mem_frameStabilizer_iff (g : SL(2, ℝ)) :
    g ∈ frameStabilizer ↔ g 1 0 = 0 ∧ g 0 1 = 0 := by
  change g • baseBoundaryPair = baseBoundaryPair ↔ _
  constructor
  · intro h
    have hinfty := congrArg (fun p : BoundaryPair => p.val.1) h
    have h0 := congrArg (fun p : BoundaryPair => p.val.2) h
    change g • (∞ : OnePoint ℝ) = ∞ at hinfty
    change g • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) at h0
    have hc : g 1 0 = 0 := by
      by_contra hc
      simp [compactBoundary_smul_infty_formula, hc] at hinfty
    have hd := slTwo_lowerRight_ne_zero_of_lowerLeft_zero g hc
    have hb : g 0 1 / g 1 1 = 0 := by
      simpa [compactBoundary_smul_coe_formula, hd] using h0
    exact ⟨hc, (div_eq_zero_iff.mp hb).resolve_right hd⟩
  · rintro ⟨hc, hb⟩
    have hd := slTwo_lowerRight_ne_zero_of_lowerLeft_zero g hc
    apply Subtype.ext
    change (g • (∞ : OnePoint ℝ), g • ((0 : ℝ) : OnePoint ℝ)) = (∞, ((0 : ℝ) : OnePoint ℝ))
    simp [compactBoundary_smul_infty_formula, compactBoundary_smul_coe_formula, hc, hb, hd]

/-- The frame stabilizer is closed in the matrix group. -/
theorem isClosed_frameStabilizer : IsClosed (frameStabilizer : Set SL(2, ℝ)) := by
  have hc (i j : Fin 2) : Continuous (fun g : SL(2, ℝ) => g i j) :=
    continuous_subtype_val.matrix_elem i j
  have he : (frameStabilizer : Set SL(2, ℝ)) = {g | g 1 0 = 0} ∩ {g | g 0 1 = 0} := by
    ext g
    exact mem_frameStabilizer_iff g
  rw [he]
  exact (isClosed_eq (hc 1 0) continuous_const).inter (isClosed_eq (hc 0 1) continuous_const)

/-- Any two frame stabilizer elements commute. -/
theorem frameStabilizer_mul_comm (g h : frameStabilizer) : g * h = h * g := by
  obtain ⟨gc, gb⟩ := (mem_frameStabilizer_iff g).mp g.property
  obtain ⟨hc, hb⟩ := (mem_frameStabilizer_iff h).mp h.property
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((g : SL(2, ℝ)) * (h : SL(2, ℝ))) i j = ((h : SL(2, ℝ)) * (g : SL(2, ℝ))) i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [gc, gb, hc, hb, mul_comm]

/-- Closedness supplies a locally compact topology on the fibre group. -/
theorem frameStabilizer_locallyCompact : LocallyCompactSpace frameStabilizer := by
  let := slTwo_locallyCompactSpace
  exact isClosed_frameStabilizer.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The fibre group is Polish, so its locally finite Haar measures are sigma-finite. -/
theorem frameStabilizer_polish : PolishSpace frameStabilizer := by
  let := slTwo_polishSpace
  exact isClosed_frameStabilizer.isClosedEmbedding_subtypeVal.polishSpace

/-- Every diagonal flow time is a member of the full fibre stabilizer. -/
theorem dilationMatrix_mem_frameStabilizer (t : ℝ) : dilationMatrix t ∈ frameStabilizer := by
  rw [mem_frameStabilizer_iff]
  simp [dilationMatrix]

/-- Haar measure on the abelian fibre group is also right invariant. -/
theorem frameStabilizer_rightInvariant [MeasurableSpace frameStabilizer]
    (η : Measure frameStabilizer) [η.IsMulLeftInvariant] : η.IsMulRightInvariant := by
  constructor
  intro h
  simpa only [frameStabilizer_mul_comm] using map_mul_left_eq_self η h

/-- Joint multiplication is measurable for the inherited fibre measurable space. -/
theorem frameStabilizer_measurableMul
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)] : MeasurableMul₂ frameStabilizer := by
  let := slTwo_polishSpace
  constructor
  exact ((measurable_subtype_coe.comp measurable_fst).mul
    (measurable_subtype_coe.comp measurable_snd)).subtype_mk

/-- Fibre inversion is measurable for the inherited measurable space. -/
theorem frameStabilizer_measurableInv
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)] : MeasurableInv frameStabilizer := by
  constructor
  exact measurable_subtype_coe.inv.subtype_mk

end Singularity
