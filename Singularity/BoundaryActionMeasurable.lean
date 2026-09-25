import Singularity.BoundaryPairTransitivity
import Singularity.FiniteBoundaryChart
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Joint measurability of the full boundary action

The compact fractional-linear formula is a measurable case distinction at
infinity and at its poles. This gives joint measurability for the full real
special-linear group, not just for a countable subgroup.
-/

noncomputable section
open OnePoint Set MeasureTheory
open scoped MatrixGroups

namespace Singularity

/-- Joint measurability of the genuine compact boundary action, including the poles. -/
theorem measurable_compactBoundary_action
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)] :
    Measurable (fun p : SL(2, ℝ) × OnePoint ℝ => p.1 • p.2) := by
  classical
  have hc (i j : Fin 2) : Measurable (fun p : SL(2, ℝ) × OnePoint ℝ => p.1 i j) :=
    ((continuous_subtype_val.comp continuous_fst :
      Continuous (fun p : SL(2, ℝ) × OnePoint ℝ => (p.1 : Matrix (Fin 2) (Fin 2) ℝ))).matrix_elem i j).measurable
  have hx : Measurable (fun p : SL(2, ℝ) × OnePoint ℝ => finiteBoundaryCoordinate p.2) :=
    measurable_finiteBoundaryCoordinate.comp measurable_snd
  have he : (fun p : SL(2, ℝ) × OnePoint ℝ => p.1 • p.2) = fun p =>
      if p.2 = ∞ then
        (if p.1 1 0 = 0 then ∞ else ((p.1 0 0 / p.1 1 0 : ℝ) : OnePoint ℝ))
      else if p.1 1 0 * finiteBoundaryCoordinate p.2 + p.1 1 1 = 0 then ∞ else
        (((p.1 0 0 * finiteBoundaryCoordinate p.2 + p.1 0 1) /
          (p.1 1 0 * finiteBoundaryCoordinate p.2 + p.1 1 1) : ℝ) : OnePoint ℝ) := by
    funext p
    rcases p with ⟨g, p⟩
    cases p <;> simp [compactBoundary_smul_infty_formula, compactBoundary_smul_coe_formula,
      finiteBoundaryCoordinate_coe]
  rw [he]
  apply Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
  · exact Measurable.ite (measurableSet_eq_fun (hc 1 0) measurable_const) measurable_const
      (OnePoint.continuous_coe.measurable.comp ((hc 0 0).div (hc 1 0)))
  · exact Measurable.ite (measurableSet_eq_fun (((hc 1 0).mul hx).add (hc 1 1)) measurable_const)
      measurable_const (OnePoint.continuous_coe.measurable.comp
        ((((hc 0 0).mul hx).add (hc 0 1)).div (((hc 1 0).mul hx).add (hc 1 1))))

/-- The diagonal action on ordered distinct endpoints is jointly measurable. -/
theorem boundaryPair_measurableSMul
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)] :
    MeasurableSMul₂ SL(2, ℝ) BoundaryPair := by
  have hV : Measurable (fun p : SL(2, ℝ) × BoundaryPair => p.2.val) :=
    measurable_subtype_coe.comp measurable_snd
  have hM1 : Measurable (fun p : SL(2, ℝ) × BoundaryPair => (p.1, p.2.val.1)) :=
    measurable_fst.prodMk hV.fst
  have hM2 : Measurable (fun p : SL(2, ℝ) × BoundaryPair => (p.1, p.2.val.2)) :=
    measurable_fst.prodMk hV.snd
  have h1 := measurable_compactBoundary_action.comp hM1
  have h2 := measurable_compactBoundary_action.comp hM2
  constructor
  exact (h1.prodMk h2).subtype_mk

end Singularity
