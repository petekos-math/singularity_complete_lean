import Singularity.ProjectiveInversion

/-!
# Continuous Möbius action on the compact projective line

The existing algebraic GL(2) action extends the fractional-linear formula at
its poles. Its continuity follows by factoring it into affine homeomorphisms
and the projective inversion exchanging zero and infinity.
-/

noncomputable section
open OnePoint Matrix
open scoped Topology Classical

namespace Singularity

variable {K : Type*} [NontriviallyNormedField K]

/-- The affine homeomorphism z ↦ a z + b, extended to fix infinity. -/
def projectiveAffineHomeomorph (a : K) (ha : a ≠ 0) (b : K) : OnePoint K ≃ₜ OnePoint K :=
  ((Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)).onePointCongr

theorem projectiveAffine_coe (a : K) (ha : a ≠ 0) (b x : K) :
    projectiveAffineHomeomorph a ha b (x : OnePoint K) = ((a * x + b : K) : OnePoint K) := rfl

theorem projectiveAffine_infty (a : K) (ha : a ≠ 0) (b : K) :
    projectiveAffineHomeomorph a ha b ∞ = ∞ := rfl

/-- Nonvanishing of the inversion coefficient in the non-affine case. -/
theorem projectiveMobius_scale_ne_zero (g : GL (Fin 2) K) (hc : g 1 0 ≠ 0) :
    -(Matrix.det (g : Matrix (Fin 2) (Fin 2) K)) / (g 1 0 * g 1 0) ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr g.det_ne_zero) (mul_ne_zero hc hc)

/-- A Möbius transformation with nonzero lower-left entry factors through inversion. -/
theorem projectiveMobius_factor (g : GL (Fin 2) K) (hc : g 1 0 ≠ 0) (p : OnePoint K) :
    g • p = projectiveAffineHomeomorph
      (-(Matrix.det (g : Matrix (Fin 2) (Fin 2) K)) / (g 1 0 * g 1 0))
      (projectiveMobius_scale_ne_zero g hc) (g 0 0 / g 1 0)
      (projectiveInv (projectiveAffineHomeomorph 1 one_ne_zero (g 1 1 / g 1 0) p)) := by
  cases p with
  | infty =>
    simp [OnePoint.smul_infty_eq_ite, hc, projectiveAffine_infty,
      projectiveInv_infty, projectiveAffine_coe]
  | coe x =>
    rw [projectiveAffine_coe, one_mul, projectiveInv_coe, OnePoint.smul_some_eq_ite]
    have hz : x + g 1 1 / g 1 0 = 0 ↔ g 1 0 * x + g 1 1 = 0 := by
      field_simp
      constructor <;> intro h <;> linear_combination h
    by_cases hx : g 1 0 * x + g 1 1 = 0
    · rw [ite_eq_left hx, ite_eq_left (hz.mpr hx), projectiveAffine_infty]
    · rw [ite_eq_right hx, ite_eq_right (mt hz.mp hx), projectiveAffine_coe]
      congr 1
      rw [Matrix.det_fin_two]
      have hx' : x * g 1 0 + g 1 1 ≠ 0 := by simpa only [mul_comm] using hx
      field_simp [hc, hx, hx', mt hz.mp hx]
      ring

variable [ProperSpace K]

/-- Every algebraic GL(2) transformation of the projective line is continuous. -/
theorem continuous_projectiveMobius (g : GL (Fin 2) K) :
    Continuous (fun p : OnePoint K => g • p) := by
  by_cases hc : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := by
      intro ha
      have hd := g.det_ne_zero
      simp [Matrix.det_fin_two, ha, hc] at hd
    have hd : g 1 1 ≠ 0 := by
      intro hd
      have h := g.det_ne_zero
      simp [Matrix.det_fin_two, hd, hc] at h
    have he : (fun p : OnePoint K => g • p) =
        projectiveAffineHomeomorph (g 0 0 / g 1 1) (div_ne_zero ha hd) (g 0 1 / g 1 1) := by
      funext p
      cases p with
      | infty => simp [OnePoint.smul_infty_eq_ite, hc, projectiveAffine_infty]
      | coe x =>
        simp only [OnePoint.smul_some_eq_ite, hc, zero_mul, zero_add, hd, ite_false,
          projectiveAffine_coe]
        congr 1
        ring
    rw [he]
    exact Homeomorph.continuous _
  · have he := funext (projectiveMobius_factor g hc)
    rw [he]
    exact (Homeomorph.continuous _).comp
      (continuous_projectiveInv.comp (Homeomorph.continuous _))

/-- The genuine projective action is by homeomorphisms. -/
def projectiveMobiusHomeomorph (g : GL (Fin 2) K) : OnePoint K ≃ₜ OnePoint K where
  toEquiv := MulAction.toPerm g
  continuous_toFun := continuous_projectiveMobius g
  continuous_invFun := continuous_projectiveMobius g⁻¹

end Singularity
