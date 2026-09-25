import Singularity.ProjectiveParabolic

/-!
# Parabolics have infinite order

The only upper shear representing the identity in PSL₂ is the zero shear.
The explicit power formula therefore proves infinite order, including for
parabolics represented by negative-trace matrix lifts.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Only the zero upper shear is projectively trivial. -/
theorem slTwoProjective_shear_eq_one_iff (u : ℝ) :
    slTwoProjective (upperShearMatrix u) = 1 ↔ u = 0 := by
  rw [slTwoProjective_eq_one_iff]
  constructor
  · rintro (he | he)
    · have h := congrArg (fun a : SL(2, ℝ) => a 0 1) he
      simpa [upperShearMatrix] using h
    · have h := congrArg (fun a : SL(2, ℝ) => a 0 0) he
      norm_num [upperShearMatrix] at h
  · rintro rfl
    exact Or.inl upperShearMatrix_zero

/-- Conjugation does not alter which shear parameter represents the identity. -/
theorem slTwoProjective_conjugate_shear_eq_one_iff (B : SL(2, ℝ)) (u : ℝ) :
    slTwoProjective (B * upperShearMatrix u * B⁻¹) = 1 ↔ u = 0 := by
  constructor
  · intro h
    apply (slTwoProjective_shear_eq_one_iff u).mp
    have hh := congrArg (fun k : PSL(2, ℝ) => (slTwoProjective B)⁻¹ * k * slTwoProjective B) h
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      inv_mul_cancel, mul_one, one_mul] using hh
  · rintro rfl
    simp [upperShearMatrix_zero]

/-- Every projective parabolic has infinite order. -/
theorem ProjectiveParabolic.not_isOfFinOrder (g : PSL(2, ℝ)) (hg : ProjectiveParabolic g) :
    ¬IsOfFinOrder g := by
  obtain ⟨B, u, hu, hconj⟩ := hg.exists_conjugate_shear g
  rintro hfin
  obtain ⟨n, hn, hp⟩ := hfin.exists_pow_eq_one
  have he : slTwoProjective (B * upperShearMatrix ((n : ℝ) * u) * B⁻¹) = 1 := by
    rw [← upperShearMatrix_pow, ← conj_pow, map_pow, ← hconj]
    exact hp
  have hz := (slTwoProjective_conjugate_shear_eq_one_iff B ((n : ℝ) * u)).mp he
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_ne_zero hnp.ne' hu hz

/-- Positive powers remain parabolic. -/
theorem ProjectiveParabolic.pow (g : PSL(2, ℝ)) (hg : ProjectiveParabolic g)
    (n : ℕ) (hn : 0 < n) : ProjectiveParabolic (g ^ n) := by
  obtain ⟨B, u, _, hconj⟩ := hg.exists_conjugate_shear g
  refine ⟨?_, B * upperShearMatrix ((n : ℝ) * u) * B⁻¹, ?_, ?_⟩
  · intro he
    exact hg.not_isOfFinOrder g (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, he⟩)
  · rw [← upperShearMatrix_pow, ← conj_pow, map_pow, ← hconj]
  · rw [slTwo_trace_conjugate]
    norm_num [upperShearMatrix]

end Singularity
