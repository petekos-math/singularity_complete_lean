import Singularity.BoundaryActionMeasurable
import Singularity.LiouvilleHaarMeasureClass

/-!
# An explicit measurable section of the endpoint map

The section is defined on every distinct boundary pair, including infinity.
Its inverse is a frame with the requested inverse-frame endpoints. No choice
of an unproved measurable section is used.
-/

noncomputable section
open OnePoint Set MeasureTheory
open scoped MatrixGroups Classical

namespace Singularity

/-- A matrix sending the vertical geodesic's endpoints to the specified pair. -/
def boundaryFrameMatrix (p : BoundaryPair) : Matrix (Fin 2) (Fin 2) ℝ :=
  if p.val.1 = ∞ then !![1, finiteBoundaryCoordinate p.val.2; 0, 1]
  else if p.val.2 = ∞ then !![finiteBoundaryCoordinate p.val.1, -1; 1, 0]
  else !![finiteBoundaryCoordinate p.val.1,
    finiteBoundaryCoordinate p.val.2 / (finiteBoundaryCoordinate p.val.1 - finiteBoundaryCoordinate p.val.2);
    1, 1 / (finiteBoundaryCoordinate p.val.1 - finiteBoundaryCoordinate p.val.2)]

/-- All three branches have determinant one. -/
theorem boundaryFrameMatrix_det (p : BoundaryPair) : (boundaryFrameMatrix p).det = 1 := by
  rcases p with ⟨⟨p, q⟩, hpq⟩
  cases p with
  | infty =>
    cases q with
    | infty => exact (hpq rfl).elim
    | coe y => simp [boundaryFrameMatrix, finiteBoundaryCoordinate_coe]
  | coe x =>
    cases q with
    | infty => simp [boundaryFrameMatrix, finiteBoundaryCoordinate_coe]
    | coe y =>
      have hxy : x - y ≠ 0 := sub_ne_zero.mpr
        (fun h => hpq (congrArg (fun r : ℝ => (r : OnePoint ℝ)) h))
      simp only [boundaryFrameMatrix, coe_ne_infty, ↓reduceIte, finiteBoundaryCoordinate_coe,
        Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      field_simp

/-- The explicit special-linear boundary section. -/
def boundaryFrameSection (p : BoundaryPair) : SL(2, ℝ) :=
  ⟨boundaryFrameMatrix p, boundaryFrameMatrix_det p⟩

/-- The section has exactly the requested ordered endpoints. -/
theorem boundaryFrameSection_endpoints (p : BoundaryPair) :
    boundaryFrameSection p • baseBoundaryPair = p := by
  rcases p with ⟨⟨p, q⟩, hpq⟩
  apply Subtype.ext
  change (boundaryFrameSection _ • (∞ : OnePoint ℝ),
    boundaryFrameSection _ • ((0 : ℝ) : OnePoint ℝ)) = (p, q)
  rw [compactBoundary_smul_infty_formula, compactBoundary_smul_coe_formula]
  cases p with
  | infty =>
    cases q with
    | infty => exact (hpq rfl).elim
    | coe y => simp [boundaryFrameSection, boundaryFrameMatrix, finiteBoundaryCoordinate_coe]
  | coe x =>
    cases q with
    | infty => simp [boundaryFrameSection, boundaryFrameMatrix, finiteBoundaryCoordinate_coe]
    | coe y =>
      have hxy : x - y ≠ 0 := sub_ne_zero.mpr
        (fun h => hpq (congrArg (fun r : ℝ => (r : OnePoint ℝ)) h))
      simp [boundaryFrameSection, boundaryFrameMatrix, finiteBoundaryCoordinate_coe, hxy]

/-- The explicit matrix section is Borel measurable across its exceptional branches. -/
theorem measurable_boundaryFrameMatrix : Measurable boundaryFrameMatrix := by
  have hx : Measurable (fun p : BoundaryPair => finiteBoundaryCoordinate p.val.1) :=
    measurable_finiteBoundaryCoordinate.comp measurable_subtype_coe.fst
  have hy : Measurable (fun p : BoundaryPair => finiteBoundaryCoordinate p.val.2) :=
    measurable_finiteBoundaryCoordinate.comp measurable_subtype_coe.snd
  unfold boundaryFrameMatrix
  apply Measurable.ite (measurableSet_eq_fun measurable_subtype_coe.fst measurable_const)
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    fin_cases i <;> fin_cases j <;> first | exact hx | exact hy | exact measurable_const
  · apply Measurable.ite (measurableSet_eq_fun measurable_subtype_coe.snd measurable_const)
    · apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      fin_cases i <;> fin_cases j <;> first | exact hx | exact hy | exact measurable_const
    · apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      fin_cases i <;> fin_cases j
      · exact hx
      · exact hy.div (hx.sub hy)
      · exact measurable_const
      · exact measurable_const.div (hx.sub hy)

/-- Measurability of the determinant-one section for the Borel group structure. -/
theorem measurable_boundaryFrameSection
    [m : MeasurableSpace SL(2, ℝ)] [hm : BorelSpace SL(2, ℝ)] :
    Measurable boundaryFrameSection := by
  have he : Topology.IsClosedEmbedding (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val
  have hem := @Topology.IsClosedEmbedding.measurableEmbedding (SL(2, ℝ)) _ _ m hm _ _ _ _ he
  exact hem.measurable_comp_iff.mp measurable_boundaryFrameMatrix

/-- A section for the inverse-frame endpoint convention used on right cosets. -/
def inverseBoundaryFrameSection (p : BoundaryPair) : SL(2, ℝ) := (boundaryFrameSection p)⁻¹

theorem inverseBoundaryFrameSection_endpoints (p : BoundaryPair) :
    inverseFrameEndpoints (inverseBoundaryFrameSection p) = p := by
  simp only [inverseFrameEndpoints, inverseBoundaryFrameSection, inv_inv,
    boundaryFrameSection_endpoints]

theorem measurable_inverseBoundaryFrameSection
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)] :
    Measurable inverseBoundaryFrameSection := measurable_boundaryFrameSection.inv

end Singularity
