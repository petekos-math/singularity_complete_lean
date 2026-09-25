import Singularity.BoundaryPairs
import Singularity.ShearContraction

/-!
# Transitivity on distinct ordered boundary pairs

Explicit determinant-one matrices send (infinity, zero) to every distinct
ordered pair, including pairs containing infinity. This identifies the full
boundary-pair space as a homogeneous space for SL(2,ℝ).
-/

noncomputable section
open OnePoint Set
open scoped MatrixGroups

namespace Singularity

theorem compactBoundary_smul_infty_formula (g : SL(2, ℝ)) :
    g • (∞ : OnePoint ℝ) = if g 1 0 = 0 then ∞ else ((g 0 0 / g 1 0 : ℝ) : OnePoint ℝ) := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ g) • (∞ : OnePoint ℝ) = _
  rw [OnePoint.smul_infty_eq_ite]
  rfl

theorem compactBoundary_smul_coe_formula (g : SL(2, ℝ)) (x : ℝ) :
    g • (x : OnePoint ℝ) = if g 1 0 * x + g 1 1 = 0 then ∞ else
      (((g 0 0 * x + g 0 1) / (g 1 0 * x + g 1 1) : ℝ) : OnePoint ℝ) := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ g) • (x : OnePoint ℝ) = _
  rw [OnePoint.smul_some_eq_ite]
  rfl

/-- The ordered endpoints of the vertical geodesic. -/
def baseBoundaryPair : BoundaryPair := ⟨(∞, (0 : ℝ)), by simp⟩

/-- Explicit matrices reach every distinct ordered pair. -/
theorem exists_smul_baseBoundaryPair (p : BoundaryPair) :
    ∃ g : SL(2, ℝ), g • baseBoundaryPair = p := by
  rcases p with ⟨⟨p, q⟩, hpq⟩
  cases p with
  | infty =>
    cases q with
    | infty => exact (hpq rfl).elim
    | coe y =>
      refine ⟨upperShearMatrix y, ?_⟩
      apply Subtype.ext
      change (upperShearMatrix y • (∞ : OnePoint ℝ),
        upperShearMatrix y • ((0 : ℝ) : OnePoint ℝ)) = (∞, (y : OnePoint ℝ))
      rw [compactBoundary_smul_infty_formula, compactBoundary_smul_coe_formula]
      simp [upperShearMatrix]
  | coe x =>
    cases q with
    | infty =>
      let g : SL(2, ℝ) := ⟨!![x, -1; 1, 0], by simp⟩
      refine ⟨g, ?_⟩
      apply Subtype.ext
      change (g • (∞ : OnePoint ℝ), g • ((0 : ℝ) : OnePoint ℝ)) = ((x : OnePoint ℝ), ∞)
      rw [compactBoundary_smul_infty_formula, compactBoundary_smul_coe_formula]
      simp [g]
    | coe y =>
      have hxy : x - y ≠ 0 := sub_ne_zero.mpr (fun h => hpq (congrArg (fun r : ℝ => (r : OnePoint ℝ)) h))
      let g : SL(2, ℝ) := ⟨!![x, y / (x - y); 1, 1 / (x - y)], by
        simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]
        field_simp⟩
      refine ⟨g, ?_⟩
      apply Subtype.ext
      change (g • (∞ : OnePoint ℝ), g • ((0 : ℝ) : OnePoint ℝ)) = ((x : OnePoint ℝ), (y : OnePoint ℝ))
      rw [compactBoundary_smul_infty_formula, compactBoundary_smul_coe_formula]
      simp [g, hxy]

/-- The full special-linear action on ordered distinct endpoints is transitive. -/
theorem boundaryPair_pretransitive : MulAction.IsPretransitive SL(2, ℝ) BoundaryPair := by
  constructor
  intro p q
  obtain ⟨g, rfl⟩ := exists_smul_baseBoundaryPair p
  obtain ⟨h, hh⟩ := exists_smul_baseBoundaryPair q
  refine ⟨h * g⁻¹, ?_⟩
  simpa only [mul_smul, inv_smul_smul] using hh

end Singularity
