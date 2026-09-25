import Singularity.GreenSublinearObstruction
import Singularity.ParabolicCommonFixedPoint

/-!
# Parabolic trace classification and sublinear projective displacement

A nonidentity projective element with squared lift trace four is conjugate
to a nontrivial horizontal translation. Both possible signs of the lift are
handled explicitly. Consequently the displacement obstruction can be stated
using the parabolic trace condition, without a chosen normalization.
-/

noncomputable section
open Set Filter
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- A triangular determinant-one matrix with equal diagonal entries projects to an upper shear. -/
theorem slTwo_triangular_projective_shear (g : SL(2, ℝ))
    (hc : g 1 0 = 0) (hd : g 0 0 = g 1 1) :
    ∃ u : ℝ, slTwoProjective g = slTwoProjective (upperShearMatrix u) := by
  have hdet : g 1 1 ^ 2 = 1 := by
    have h := g.property
    simp only [Matrix.det_fin_two, hc, hd, mul_zero, sub_zero] at h
    nlinarith
  rcases sq_eq_one_iff.mp hdet with hpos | hneg
  · have he : g = upperShearMatrix (g 0 1) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [upperShearMatrix, hc, hd, hpos]
    exact ⟨g 0 1, congrArg slTwoProjective he⟩
  · have he : g = (-1 : SL(2, ℝ)) * upperShearMatrix (-g 0 1) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp [upperShearMatrix, hc, hd, hneg]
    refine ⟨-g 0 1, ?_⟩
    calc
      slTwoProjective g = slTwoProjective ((-1 : SL(2, ℝ)) * upperShearMatrix (-g 0 1)) :=
        congrArg slTwoProjective he
      _ = _ := by rw [map_mul, (slTwoProjective_eq_one_iff _).mpr (Or.inr rfl), one_mul]

/-- Squared trace four permits normalization of the projective element as a shear. -/
theorem slTwo_trace_four_projective_conjugate_shear (g : SL(2, ℝ))
    (htrace : (g 0 0 + g 1 1) ^ 2 = 4) :
    ∃ (B : SL(2, ℝ)) (u : ℝ), slTwoProjective g =
      slTwoProjective (B * upperShearMatrix u * B⁻¹) := by
  obtain ⟨B, hc, hd⟩ : ∃ B : SL(2, ℝ), (B⁻¹ * g * B) 1 0 = 0 ∧
      (B⁻¹ * g * B) 0 0 = (B⁻¹ * g * B) 1 1 := by
    by_cases hc : g 1 0 = 0
    · have hdet : g 0 0 * g 1 1 = 1 := by
        simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using g.property
      have hd : g 0 0 = g 1 1 := by nlinarith [sq_nonneg (g 0 0 - g 1 1)]
      exact ⟨1, by simpa using hc, by simpa using hd⟩
    · obtain ⟨B, hb, hd, _⟩ := slTwo_parabolic_normalization g htrace hc
      exact ⟨B, hb, hd⟩
  obtain ⟨u, hu⟩ := slTwo_triangular_projective_shear (B⁻¹ * g * B) hc hd
  refine ⟨B, u, ?_⟩
  calc
    slTwoProjective g = slTwoProjective (B * (B⁻¹ * g * B) * B⁻¹) := by
      congr 1
      group
    _ = _ := by
      simpa only [map_mul] using congrArg
        (fun h : PSL(2, ℝ) => slTwoProjective B * h * slTwoProjective B⁻¹) hu

/-- The parabolic trace condition, excluding the identity projective transformation. -/
def ProjectiveParabolic (g : PSL(2, ℝ)) : Prop :=
  g ≠ 1 ∧ ∃ a : SL(2, ℝ), slTwoProjective a = g ∧ (a 0 0 + a 1 1) ^ 2 = 4

/-- Every parabolic projective element is conjugate to a nontrivial horizontal translation. -/
theorem ProjectiveParabolic.exists_conjugate_shear (g : PSL(2, ℝ)) (hg : ProjectiveParabolic g) :
    ∃ (B : SL(2, ℝ)) (u : ℝ), u ≠ 0 ∧ g = slTwoProjective (B * upperShearMatrix u * B⁻¹) := by
  obtain ⟨hne, a, ha, htrace⟩ := hg
  obtain ⟨B, u, hu⟩ := slTwo_trace_four_projective_conjugate_shear a htrace
  refine ⟨B, u, ?_, ha.symm.trans hu⟩
  intro hz
  subst u
  simp only [upperShearMatrix_zero, mul_one, mul_inv_cancel, map_one] at hu
  exact hne (ha.symm.trans hu)

/-- The displacement of every parabolic element is sublinear, with no normalization hypothesis. -/
theorem ProjectiveParabolic.displacement_sublinear (g : PSL(2, ℝ))
    (hg : ProjectiveParabolic g) (z : ℍ) :
    Tendsto (fun n : ℕ => dist z (g ^ n • z) / (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨B, u, _, hu⟩ := hg.exists_conjugate_shear g
  exact projective_parabolic_displacement_sublinear g B u hu z

/-- The trace-based parabolic condition and linear word growth obstruct bounded
Green/geometric comparison. Undistortion remains an explicit hypothesis. -/
theorem projective_parabolic_trace_green_obstruction (Γ : Subgroup PSL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ)))
    (κ E : ℝ) (hκ : 0 < κ)
    (hword : ∀ n : ℕ, κ * n - E ≤ (wordDistance s hgen 1 (g ^ n) : ℝ)) (z : ℍ) :
    ¬∃ δ C : ℝ, ∀ x : Γ, |greenDistance s μ 1 x - δ * dist z (x • z)| ≤ C := by
  obtain ⟨B, u, _, hu⟩ := hpar.exists_conjugate_shear g
  exact projective_parabolic_green_comparison_obstruction Γ hne s μ hpos hmass hgen
    g B u hu κ E hκ hword z

end Singularity
