import Singularity.PoissonInversion
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Poisson covariance and the upper-half-plane Möbius action

The real-chart boundary transformations are understood modulo their finitely
many exceptional points. The Poisson measures are absolutely continuous, so
these exceptional values do not affect their pushforwards.
-/

noncomputable section
open MeasureTheory Set UpperHalfPlane
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

theorem poissonBoundaryMeasure_translate (a : ℝ) (z : ℍ) :
    Measure.map (fun u : ℝ => a + u) (poissonBoundaryMeasure z) =
      poissonBoundaryMeasure (a +ᵥ z) := by
  simpa only [poissonBoundaryMeasure, vadd_re, vadd_im] using
    halfPlanePoissonMeasure_translate z.re z.im a

theorem poissonBoundaryMeasure_dilate (a : {a : ℝ // 0 < a}) (z : ℍ) :
    Measure.map (fun u : ℝ => (a : ℝ) * u) (poissonBoundaryMeasure z) =
      poissonBoundaryMeasure (a • z) := by
  simpa only [poissonBoundaryMeasure, Real.exp_log a.property, pos_real_re, pos_real_im] using
    halfPlanePoissonMeasure_dilation z.re z.im (Real.log a.val)

theorem poissonBoundaryMeasure_invert (z : ℍ) :
    Measure.map boundaryInversion (poissonBoundaryMeasure z) =
      poissonBoundaryMeasure (ModularGroup.S • z) := by
  rw [poissonBoundaryMeasure, halfPlanePoissonMeasure_inversion z.re z.im_pos]
  simp only [poissonBoundaryMeasure, modular_S_smul, mk_re, mk_im, Complex.inv_re,
    Complex.inv_im, Complex.neg_re, Complex.neg_im, Complex.normSq_neg, neg_neg]
  simp only [Complex.normSq_apply, pow_two, coe_re, coe_im]

/-- The positive dilation/translation/inversion word used in the Bruhat
factorization of a real special linear matrix. -/
theorem poissonBoundaryMeasure_word (a : {a : ℝ // 0 < a}) (v w : ℝ) (z : ℍ) :
    Measure.map (fun u : ℝ => w + boundaryInversion (v + (a : ℝ) * u))
      (poissonBoundaryMeasure z) =
      poissonBoundaryMeasure (w +ᵥ (ModularGroup.S • (v +ᵥ (a • z)))) := by
  have h := poissonBoundaryMeasure_dilate a z
  have h' := congrArg (Measure.map (fun u : ℝ => v + u)) h
  rw [Measure.map_map (measurable_const_add v) (measurable_const_mul _),
    poissonBoundaryMeasure_translate] at h'
  have h'' := congrArg (Measure.map boundaryInversion) h'
  rw [Measure.map_map measurable_boundaryInversion
    ((measurable_const_add v).comp (measurable_const_mul _)),
    poissonBoundaryMeasure_invert] at h''
  have h''' := congrArg (Measure.map (fun u : ℝ => w + u)) h''
  rw [Measure.map_map (measurable_const_add w)
    (measurable_boundaryInversion.comp ((measurable_const_add v).comp (measurable_const_mul _))),
    poissonBoundaryMeasure_translate] at h'''
  exact h'''

/-- The finite real-chart formula for the projective action of a special linear matrix. -/
def realBoundaryMobius (g : SL(2, ℝ)) (u : ℝ) : ℝ :=
  (g 0 0 * u + g 0 1) / (g 1 0 * u + g 1 1)

theorem measurable_realBoundaryMobius (g : SL(2, ℝ)) : Measurable (realBoundaryMobius g) := by
  unfold realBoundaryMobius
  fun_prop

/-- Poisson covariance for an affine boundary word. -/
theorem poissonBoundaryMeasure_affine (a : {a : ℝ // 0 < a}) (v : ℝ) (z : ℍ) :
    Measure.map (fun u : ℝ => v + (a : ℝ) * u) (poissonBoundaryMeasure z) =
      poissonBoundaryMeasure (v +ᵥ (a • z)) := by
  have h := congrArg (Measure.map (fun u : ℝ => v + u)) (poissonBoundaryMeasure_dilate a z)
  rw [Measure.map_map (measurable_const_add v) (measurable_const_mul _),
    poissonBoundaryMeasure_translate] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Full covariance under the real special linear group. The real-chart pole
is a singleton of measure zero, handled explicitly in the proof. -/
theorem poissonBoundaryMeasure_mobius (g : SL(2, ℝ)) (z : ℍ) :
    Measure.map (realBoundaryMobius g) (poissonBoundaryMeasure z) =
      poissonBoundaryMeasure (g • z) := by
  by_cases hc : g 1 0 = 0
  · obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
    let G : SL(2, ℝ) := ⟨!![a, b; 0, a⁻¹], by simp [ha]⟩
    change Measure.map (realBoundaryMobius G) (poissonBoundaryMeasure z) = poissonBoundaryMeasure (G • z)
    let A : {a : ℝ // 0 < a} := ⟨a * a, mul_self_pos.mpr ha⟩
    have hb : realBoundaryMobius G =
        (fun u => b * a + (A : ℝ) * u) := by
      funext u
      simp [realBoundaryMobius, G, A, div_inv_eq_mul]
      ring
    have hp : G • z = b * a +ᵥ (A • z) := by
      apply UpperHalfPlane.ext
      simp [coe_specialLinearGroup_apply, G, A, Complex.real_smul, add_mul]
      ring
    rw [hb, poissonBoundaryMeasure_affine, hp]
  · induction g using Matrix.SpecialLinearGroup.fin_two_induction with | h a b c d hdet =>
    have hc' : c ≠ 0 := by simpa using hc
    let G : SL(2, ℝ) := ⟨!![a, b; c, d], by simpa using hdet⟩
    change Measure.map (realBoundaryMobius G) (poissonBoundaryMeasure z) = poissonBoundaryMeasure (G • z)
    let A : {a : ℝ // 0 < a} := ⟨c * c, mul_self_pos.mpr hc'⟩
    have hp : G • z =
        a / c +ᵥ (ModularGroup.S • (c * d +ᵥ (A • z))) := by
      rw [modular_S_smul]
      apply UpperHalfPlane.ext
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc'
      have hdC : (c : ℂ) * (z : ℂ) + d ≠ 0 :=
        UpperHalfPlane.linear_ne_zero (cd := ![c, d]) z (by
          intro h
          apply hc'
          simpa using congrFun h 0)
      have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
      suffices ((a : ℂ) * z + b) / ((c : ℂ) * z + d) =
          (a : ℂ) / c - ((c : ℂ) * d + c * c * z)⁻¹ by
        simp [coe_specialLinearGroup_apply, G, A, Complex.real_smul]
        rw [show -((c : ℂ) * c * z) + -((c : ℂ) * d) =
          -((c : ℂ) * d + c * c * z) by ring, inv_neg]
        simpa only [sub_eq_add_neg] using this
      grind
    have hb : realBoundaryMobius G =ᵐ[volume]
        (fun u => a / c + boundaryInversion (c * d + (A : ℝ) * u)) := by
      have hz : ∀ᵐ u : ℝ ∂volume, u ≠ -d / c := by simp [ae_iff]
      filter_upwards [hz] with u hu
      have hd : c * u + d ≠ 0 := by
        intro hh
        apply hu
        apply (eq_div_iff hc').mpr
        nlinarith
      change (a * u + b) / (c * u + d) = a / c + -(c * d + c * c * u)⁻¹
      grind
    have hac : poissonBoundaryMeasure z ≪ volume :=
      (halfPlanePoissonMeasure_measureClass z.re z.im_pos).1
    rw [Measure.map_congr (hac.ae_eq hb), poissonBoundaryMeasure_word, hp]

end Singularity
