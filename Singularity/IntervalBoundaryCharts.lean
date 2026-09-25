import Singularity.ChartBoundaryArcs
import Singularity.BoundaryPairTransitivity

/-!
# Oriented charts for bounded ideal intervals

The chart sends infinity to the left endpoint and zero to the right
endpoint. Its negative ideal side is the bounded interval between them.
The endpoint order matters: reversing it selects the complementary arc.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- A determinant-one chart whose negative side faces the interval (l,r). -/
def intervalBoundaryNormalizer (l r : ℝ) (h : l < r) : SL(2, ℝ) :=
  ⟨!![1, -r; 1 / (r - l), -l / (r - l)], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp [sub_ne_zero.mpr (ne_of_gt h)]
    ring⟩

/-- The inverse normalizer carries the negative arc to the bounded interval. -/
def intervalBoundaryChart (l r : ℝ) (h : l < r) : SL(2, ℝ) :=
  (intervalBoundaryNormalizer l r h)⁻¹

/-- The inverse chart's fractional-linear formula away from the left endpoint. -/
theorem intervalBoundaryChart_inv_smul_coe (l r : ℝ) (h : l < r)
    (x : ℝ) (hx : x ≠ l) :
    (intervalBoundaryChart l r h)⁻¹ • (x : OnePoint ℝ) =
      (((r - l) * (x - r) / (x - l) : ℝ) : OnePoint ℝ) := by
  have hrl : r - l ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  have hxl : x - l ≠ 0 := sub_ne_zero.mpr hx
  have hd : 1 / (r - l) * x + -l / (r - l) ≠ 0 := by
    have he : 1 / (r - l) * x + -l / (r - l) = (x - l) / (r - l) := by ring
    rw [he]
    exact div_ne_zero hxl hrl
  rw [intervalBoundaryChart, inv_inv, compactBoundary_smul_coe_formula]
  simp only [intervalBoundaryNormalizer, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, ite_eq_right hd, one_mul]
  congr 1
  rw [show 1 / (r - l) * x + -l / (r - l) = (x - l) / (r - l) by ring]
  field_simp [hrl, hxl]
  ring

/-- Infinity has a strictly positive finite inverse-chart coordinate. -/
theorem intervalBoundaryChart_inv_smul_infty (l r : ℝ) (h : l < r) :
    (intervalBoundaryChart l r h)⁻¹ • (∞ : OnePoint ℝ) = ((r - l : ℝ) : OnePoint ℝ) := by
  rw [intervalBoundaryChart, inv_inv, compactBoundary_smul_infty_formula]
  simp [intervalBoundaryNormalizer, sub_ne_zero.mpr (ne_of_gt h)]

/-- The chart's endpoints are ordered left to right as infinity and zero. -/
theorem intervalBoundaryChart_endpoints (l r : ℝ) (h : l < r) :
    intervalBoundaryChart l r h • (∞ : OnePoint ℝ) = (l : OnePoint ℝ) ∧
      intervalBoundaryChart l r h • ((0 : ℝ) : OnePoint ℝ) = (r : OnePoint ℝ) := by
  have hl : (intervalBoundaryChart l r h)⁻¹ • (l : OnePoint ℝ) = ∞ := by
    rw [intervalBoundaryChart, inv_inv, compactBoundary_smul_coe_formula]
    simp only [intervalBoundaryNormalizer, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have he : 1 / (r - l) * l + -l / (r - l) = 0 := by ring
    rw [ite_eq_left he]
  have hr : (intervalBoundaryChart l r h)⁻¹ • (r : OnePoint ℝ) = (0 : ℝ) := by
    rw [intervalBoundaryChart_inv_smul_coe l r h r (ne_of_gt h)]
    simp
  constructor
  · rw [← hl, smul_inv_smul]
  · rw [← hr, smul_inv_smul]

/-- Every interior point of (l,r) has a negative finite chart coordinate. -/
theorem intervalBoundaryChart_negative_coordinate (l r : ℝ) (h : l < r)
    {x : ℝ} (hx : x ∈ Ioo l r) :
    ∃ t : ℝ, t < 0 ∧ (intervalBoundaryChart l r h)⁻¹ • (x : OnePoint ℝ) = (t : OnePoint ℝ) := by
  refine ⟨(r - l) * (x - r) / (x - l), ?_, intervalBoundaryChart_inv_smul_coe l r h x (ne_of_gt hx.1)⟩
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sub_pos.mpr h) (sub_neg.mpr hx.2))
    (sub_pos.mpr hx.1)

/-- The closed nonpositive chart arc is contained in the bounded endpoint interval. -/
theorem chartNonpositiveBoundaryArc_interval_subset (l r : ℝ) (h : l < r) :
    chartNonpositiveBoundaryArc (intervalBoundaryChart l r h) ⊆
      ((↑) : ℝ → OnePoint ℝ) '' Icc l r := by
  intro ξ hξ
  change (intervalBoundaryChart l r h)⁻¹ • ξ ∉ ((↑) : ℝ → OnePoint ℝ) '' Ioi 0 at hξ
  cases ξ with
  | infty =>
    exact (hξ ⟨r - l, sub_pos.mpr h, (intervalBoundaryChart_inv_smul_infty l r h).symm⟩).elim
  | coe x =>
    refine ⟨x, ?_, rfl⟩
    by_contra hx
    have hxout : x < l ∨ r < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hx
    have hxl : x ≠ l := by rcases hxout with hx | hx <;> linarith
    have hp : 0 < (r - l) * (x - r) / (x - l) := by
      rcases hxout with hx | hx
      · exact div_pos_of_neg_of_neg
          (mul_neg_of_pos_of_neg (sub_pos.mpr h) (sub_neg.mpr (hx.trans h))) (sub_neg.mpr hx)
      · exact div_pos (mul_pos (sub_pos.mpr h) (sub_pos.mpr hx)) (sub_pos.mpr (h.trans hx))
    exact hξ ⟨_, hp, (intervalBoundaryChart_inv_smul_coe l r h x hxl).symm⟩

end Singularity
