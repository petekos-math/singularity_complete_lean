import Singularity.CurrentFrameLift
import Singularity.ShearContraction

/-!
# Endpoint sections adapted to the contracting horocycles

The first row of this frame section depends only on the forward endpoint.
Consequently, at fixed forward endpoint and fixed signed diagonal fibre,
changing the backward endpoint moves along a lower horocycle. This is the
product structure needed for one-sided measure transfer; the backward endpoint
is not identified with the additive shear parameter.
-/

noncomputable section
open MeasureTheory OnePoint
open scoped MatrixGroups Classical

namespace Singularity

/-- A determinant-one frame matrix with a forward-endpoint-dependent first row. -/
def stableFrameMatrix (p : BoundaryPair) : Matrix (Fin 2) (Fin 2) ℝ :=
  if p.val.2 = ∞ then !![0, 1; -1, finiteBoundaryCoordinate p.val.1]
  else if p.val.1 = ∞ then !![1, -finiteBoundaryCoordinate p.val.2; 0, 1]
  else !![1, -finiteBoundaryCoordinate p.val.2;
    1 / (finiteBoundaryCoordinate p.val.2 - finiteBoundaryCoordinate p.val.1),
    -finiteBoundaryCoordinate p.val.1 /
      (finiteBoundaryCoordinate p.val.2 - finiteBoundaryCoordinate p.val.1)]

theorem stableFrameMatrix_det (p : BoundaryPair) : (stableFrameMatrix p).det = 1 := by
  rcases p with ⟨⟨p, q⟩, hpq⟩
  cases p with
  | infty =>
    cases q with
    | infty => exact (hpq rfl).elim
    | coe y => simp [stableFrameMatrix, finiteBoundaryCoordinate_coe]
  | coe x =>
    cases q with
    | infty => simp [stableFrameMatrix, finiteBoundaryCoordinate_coe]
    | coe y =>
      have hxy : y - x ≠ 0 := sub_ne_zero.mpr
        (fun h => hpq (congrArg (fun r : ℝ => (r : OnePoint ℝ)) h.symm))
      simp only [stableFrameMatrix, coe_ne_infty, ↓reduceIte, finiteBoundaryCoordinate_coe,
        Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      field_simp
      ring

/-- A global frame section adapted to stable rather than additive-shear coordinates. -/
def stableFrameSection (p : BoundaryPair) : SL(2, ℝ) :=
  ⟨stableFrameMatrix p, stableFrameMatrix_det p⟩

theorem stableFrameSection_endpoints (p : BoundaryPair) :
    inverseFrameEndpoints (stableFrameSection p) = p := by
  rcases p with ⟨⟨p, q⟩, hpq⟩
  apply Subtype.ext
  change ((stableFrameSection _)⁻¹ • (∞ : OnePoint ℝ),
    (stableFrameSection _)⁻¹ • ((0 : ℝ) : OnePoint ℝ)) = (p, q)
  rw [compactBoundary_smul_infty_formula, compactBoundary_smul_coe_formula]
  simp only [Matrix.SpecialLinearGroup.SL2_inv_expl]
  cases p with
  | infty =>
    cases q with
    | infty => exact (hpq rfl).elim
    | coe y => simp [stableFrameSection, stableFrameMatrix, finiteBoundaryCoordinate_coe]
  | coe x =>
    cases q with
    | infty => simp [stableFrameSection, stableFrameMatrix, finiteBoundaryCoordinate_coe]
    | coe y =>
      have hxy : y - x ≠ 0 := sub_ne_zero.mpr
        (fun h => hpq (congrArg (fun r : ℝ => (r : OnePoint ℝ)) h.symm))
      simp [stableFrameSection, stableFrameMatrix, finiteBoundaryCoordinate_coe, hxy]
      field_simp

/-- Equality of forward endpoints forces equality of the section's first rows. -/
theorem stableFrameSection_firstRow (p q : BoundaryPair) (h : p.val.2 = q.val.2)
    (j : Fin 2) : stableFrameSection p 0 j = stableFrameSection q 0 j := by
  by_cases hq : q.val.2 = ∞
  · fin_cases j <;> simp [stableFrameSection, stableFrameMatrix, h, hq]
  · by_cases hp : p.val.1 = ∞ <;> by_cases hq₁ : q.val.1 = ∞ <;>
      fin_cases j <;> simp [stableFrameSection, stableFrameMatrix, h, hq, hp, hq₁]

theorem measurable_stableFrameMatrix : Measurable stableFrameMatrix := by
  have hx : Measurable (fun p : BoundaryPair => finiteBoundaryCoordinate p.val.1) :=
    measurable_finiteBoundaryCoordinate.comp measurable_subtype_coe.fst
  have hy : Measurable (fun p : BoundaryPair => finiteBoundaryCoordinate p.val.2) :=
    measurable_finiteBoundaryCoordinate.comp measurable_subtype_coe.snd
  unfold stableFrameMatrix
  apply Measurable.ite (measurableSet_eq_fun measurable_subtype_coe.snd measurable_const)
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    fin_cases i <;> fin_cases j <;> first | exact hx | exact measurable_const
  · apply Measurable.ite (measurableSet_eq_fun measurable_subtype_coe.fst measurable_const)
    · apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      fin_cases i <;> fin_cases j <;> first | exact hy.neg | exact measurable_const
    · apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      fin_cases i <;> fin_cases j
      · exact measurable_const
      · exact hy.neg
      · exact measurable_const.div (hy.sub hx)
      · exact hx.neg.div (hy.sub hx)

theorem measurable_stableFrameSection
    [m : MeasurableSpace SL(2, ℝ)] [hm : BorelSpace SL(2, ℝ)] :
    Measurable stableFrameSection := by
  have he : Topology.IsClosedEmbedding (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val
  have hem := @Topology.IsClosedEmbedding.measurableEmbedding (SL(2, ℝ)) _ _ m hm _ _ _ _ he
  exact hem.measurable_comp_iff.mp measurable_stableFrameMatrix

/-- Two special-linear matrices with the same first row differ by a lower shear. -/
theorem exists_lowerShear_of_firstRow_eq (g h : SL(2, ℝ))
    (hr : ∀ j, h 0 j = g 0 j) : ∃ u : ℝ, h = lowerShearMatrix u * g := by
  let a := h * g⁻¹
  have ha0 : a 0 0 = 1 := by
    have hd := g.property
    rw [Matrix.det_fin_two] at hd
    simpa [a, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hr, sub_eq_add_neg] using hd
  have ha1 : a 0 1 = 0 := by
    simp [a, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hr, mul_comm]
  have ha11 : a 1 1 = 1 := by
    have hd := a.property
    rw [Matrix.det_fin_two] at hd
    simpa only [ha0, ha1, one_mul, zero_mul, sub_zero] using hd
  have he : a = lowerShearMatrix (a 1 0) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [lowerShearMatrix, ha0, ha1, ha11]
  refine ⟨a 1 0, ?_⟩
  rw [← he]
  simp [a, mul_assoc]

/-- Reassemble the stable section with the full signed diagonal fibre. -/
def stableFrameFromCoordinates (q : BoundaryPair × frameStabilizer) : SL(2, ℝ) :=
  (q.2 : SL(2, ℝ)) * stableFrameSection q.1

/-- The transverse coordinates are the forward endpoint and the diagonal fibre. -/
theorem stableFrameFromCoordinates_fibre (p q : BoundaryPair) (h : frameStabilizer)
    (hpq : p.val.2 = q.val.2) : ∃ u : ℝ,
    stableFrameFromCoordinates (q, h) = lowerShearMatrix u * stableFrameFromCoordinates (p, h) := by
  apply exists_lowerShear_of_firstRow_eq
  intro j
  have hb := ((mem_frameStabilizer_iff h).mp h.property).2
  simp only [stableFrameFromCoordinates, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, hb, zero_mul, add_zero]
  rw [stableFrameSection_firstRow q p hpq.symm]

section Measurable
variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
attribute [local instance] slTwo_polishSpace frameStabilizer_measurableMul frameStabilizer_measurableInv

theorem measurable_stableFrameFromCoordinates : Measurable stableFrameFromCoordinates :=
  (measurable_subtype_coe.comp measurable_snd).mul
    (measurable_stableFrameSection.comp measurable_fst)

/-- Replacing the original section by the stable section leaves every current lift unchanged. -/
theorem currentFrameLift_stable_coordinates (J : Measure BoundaryPair)
    (η : Measure frameStabilizer) [SFinite J] [SFinite η] [η.IsMulRightInvariant] :
    (J.prod η).map stableFrameFromCoordinates = currentFrameLift J η :=
  currentFrameLift_section_independent J η stableFrameSection measurable_stableFrameSection
    stableFrameSection_endpoints

end Measurable
end Singularity
