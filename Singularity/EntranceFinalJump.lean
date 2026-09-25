import Singularity.RelativeLastEntrance

/-!
# The final jump into a stopping set

First entrance at a boundary vertex consists of the time-zero contribution
and a path killed on that set followed by one final jump. We derive the formula
from uniqueness of the counting-L² Dirichlet problem.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

omit [Countable Γ] in
/-- A Markov operator sends a point source to its finitely many predecessors. -/
theorem rightMarkov_delta_predecessors (s : Finset Γ) (μ : Γ → ℝ) (a : Γ) :
    rightMarkov s μ (countingDelta a) =
      ∑ g ∈ s, (μ g : ℂ) • countingDelta (a * g⁻¹) := by
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro x
  rw [rightMarkov_apply, ← countingEvaluation_apply]
  simp only [map_sum, map_smul, countingEvaluation_apply, countingDelta_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro g hg
  rw [eq_mul_inv_iff_mul_eq]

variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (A : Set Γ)

/-- The first-entrance column is a point source plus a killed potential. -/
theorem firstEntranceColumn_final_jump {a : Γ} (ha : a ∈ A) :
    firstEntranceColumn s μ hμ hgap A a = countingDelta a +
      killedGreenOperator s μ hμ hmass hgap A (rightMarkov s μ (countingDelta a)) := by
  apply harmonic_eq_of_boundary_eq (rightMarkov s μ)
    (rightMarkov_contraction s μ hμ hmass) hgap A
  · intro x hx
    rw [firstEntranceColumn_boundary s μ hμ hgap A a hx, counting_add_apply]
    have hb := supportedRestriction_apply A
      (killedGreenOperator s μ hμ hmass hgap A (rightMarkov s μ (countingDelta a))) ⟨x, hx⟩
    rw [killedGreenOperator_boundary] at hb
    have hz : (0 : GroupL2 Γ) x = 0 := by
      simpa only [countingEvaluation_apply] using (countingEvaluation x).map_zero
    have hk := hb.symm.trans hz
    rw [hk, add_zero]
  · intro x hx
    exact firstEntranceColumn_harmonic s μ hμ hgap A a hx
  · intro x hx
    have hd := killedGreenOperator_defect s μ hμ hmass hgap A
      (rightMarkov s μ (countingDelta a)) hx
    rw [counting_sub_apply] at hd
    have hxa : x ≠ a := fun h => hx (h ▸ ha)
    have hz : countingDelta a x = 0 := by simp [countingDelta_apply, hxa]
    rw [map_add, counting_add_apply, counting_add_apply, hz, zero_add]
    linear_combination -hd

include hμ hmass hgap in
/-- Exact finite final-jump formula, including entrance at time zero. -/
theorem firstEntranceKernel_final_jump {a : Γ} (ha : a ∈ A) (x : Γ) :
    firstEntranceKernel s μ A x a = (if x = a then 1 else 0) +
      ∑ g ∈ s, μ g * killedGreen s μ A x (a * g⁻¹) := by
  have he := congrArg (countingEvaluation x)
    (firstEntranceColumn_final_jump s μ hμ hmass hgap A ha)
  rw [rightMarkov_delta_predecessors] at he
  simp only [map_add, map_sum, map_smul, countingEvaluation_apply,
    firstEntranceColumn_apply, killedGreenOperator_coefficient, countingDelta_apply,
    smul_eq_mul] at he
  apply Complex.ofReal_injective
  push_cast
  simpa only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero] using he

end Singularity
