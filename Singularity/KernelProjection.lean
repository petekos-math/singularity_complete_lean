import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Tactic

/-!
# Measurable projections onto kernels

We use the mean ergodic theorem to construct the projection onto ker B as a
pointwise limit of Cesàro averages of I - (1 + ‖B‖²)⁻¹ B*B. This replaces the
resolvent regularization in the writeup; the resulting projection is the same.
-/

noncomputable section
open Filter TopologicalSpace
open scoped Topology

namespace Singularity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A positive step size, continuously depending on B. -/
def kernelStepSize (B : E →L[ℂ] F) : ℝ := (1 + ‖B‖ ^ 2)⁻¹

omit [CompleteSpace E] [CompleteSpace F] in
theorem kernelStepSize_pos (B : E →L[ℂ] F) : 0 < kernelStepSize B := by
  unfold kernelStepSize
  positivity

/-- A contraction whose fixed subspace is ker B. -/
def kernelContraction (B : E →L[ℂ] F) : E →L[ℂ] E :=
  1 - (kernelStepSize B : ℂ) • (B.adjoint.comp B)

theorem kernelContraction_apply (B : E →L[ℂ] F) (x : E) :
    kernelContraction B x = x - (kernelStepSize B : ℂ) • B.adjoint (B x) := rfl

/-- The elementary norm estimate behind the projection approximation. -/
theorem kernelContraction_norm_le (B : E →L[ℂ] F) : ‖kernelContraction B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, kernelContraction_apply]
  let a := kernelStepSize B
  have ha : 0 < a := kernelStepSize_pos B
  have hae : a * (1 + ‖B‖ ^ 2) = 1 := inv_mul_cancel₀ (by positivity)
  have haB : a * ‖B‖ ^ 2 ≤ 1 := by nlinarith
  have hnorm : ‖B.adjoint (B x)‖ ≤ ‖B‖ * ‖B x‖ := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using B.adjoint.le_opNorm (B x)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow] at hsq
  have hscale := mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
  have ha2 : a ^ 2 * ‖B‖ ^ 2 ≤ a := by nlinarith
  have hscale2 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg ‖B x‖)
  have hi : (inner ℂ x (B.adjoint (B x))).re = ‖B x‖ ^ 2 := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (B x)).symm
  have his : RCLike.re (inner ℂ x ((a : ℂ) • B.adjoint (B x))) = a * ‖B x‖ ^ 2 := by
    rw [inner_smul_right]
    change ((a : ℂ) * inner ℂ x (B.adjoint (B x))).re = _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hi]
  have hid := norm_sub_sq (𝕜 := ℂ) x ((a : ℂ) • B.adjoint (B x))
  rw [his] at hid
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow] at hid
  have hsq_le : ‖x - (a : ℂ) • B.adjoint (B x)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [mul_nonneg ha.le (sq_nonneg ‖B x‖)]
  nlinarith [norm_nonneg x, norm_nonneg (x - (a : ℂ) • B.adjoint (B x))]

/-- Fixed points are precisely kernel vectors. -/
theorem kernelContraction_fixed_iff (B : E →L[ℂ] F) (x : E) :
    kernelContraction B x = x ↔ B x = 0 := by
  rw [kernelContraction_apply]
  constructor
  · intro h
    have hs : (kernelStepSize B : ℂ) • B.adjoint (B x) = 0 := sub_eq_self.mp h
    have ha : (kernelStepSize B : ℂ) ≠ 0 := by exact_mod_cast (kernelStepSize_pos B).ne'
    have hz : B.adjoint (B x) = 0 := (smul_eq_zero.mp hs).resolve_left ha
    have hi : inner ℂ (B x) (B x) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hz, inner_zero_right]
    exact inner_self_eq_zero.mp hi
  · intro h
    simp [h]

/-- Orthogonal projection onto the closed kernel, with values in the ambient space. -/
def kernelProjection (B : E →L[ℂ] F) : E →L[ℂ] E :=
  B.ker.subtypeL.comp B.ker.orthogonalProjectionOnto

omit [CompleteSpace E] in
/-- Equality of subspaces implies equality of their ambient projections. -/
theorem orthogonalProjection_congr {S T : Submodule ℂ E}
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] (h : S = T) (x : E) :
    (S.orthogonalProjectionOnto x : E) = (T.orthogonalProjectionOnto x : E) := by
  subst T
  rfl

/-- The mean-ergodic approximants converge to the kernel projection. -/
theorem kernelProjection_tendsto (B : E →L[ℂ] F) (x : E) :
    Tendsto (birkhoffAverage ℂ (kernelContraction B) id · x) atTop
      (𝓝 (kernelProjection B x)) := by
  have heq : (kernelContraction B).toLinearMap.eqLocus
      (1 : E →L[ℂ] E).toLinearMap = B.toLinearMap.ker := by
    ext x
    exact kernelContraction_fixed_iff B x
  have h := (kernelContraction B).tendsto_birkhoffAverage_orthogonalProjection
    (kernelContraction_norm_le B) x
  rw [orthogonalProjection_congr heq x] at h
  exact h

omit [CompleteSpace F] in
/-- Every projected vector lies in ker B. -/
theorem kernelProjection_mem (B : E →L[ℂ] F) (x : E) :
    B (kernelProjection B x) = 0 :=
  (B.ker.orthogonalProjectionOnto x).property

omit [CompleteSpace F] in
/-- Projection fixes kernel vectors. -/
theorem kernelProjection_eq_self (B : E →L[ℂ] F) {x : E} (hx : B x = 0) :
    kernelProjection B x = x := by
  exact congrArg Subtype.val (B.ker.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩)

/-- The approximation operator varies continuously with B. -/
theorem continuous_kernelContraction :
    Continuous (kernelContraction : (E →L[ℂ] F) → E →L[ℂ] E) := by
  have ha : Continuous (fun B : E →L[ℂ] F => (kernelStepSize B : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    change Continuous (fun B : E →L[ℂ] F => (1 + ‖B‖ ^ 2)⁻¹)
    exact ((continuous_const : Continuous (fun _ : E →L[ℂ] F => (1 : ℝ))).add
      (continuous_norm.pow 2)).inv₀ (fun B => by
        change (1 : ℝ) + ‖B‖ ^ 2 ≠ 0
        exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)))
  exact continuous_const.sub (ha.smul
    (ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id))

/-- Each approximating vector varies continuously with B. -/
theorem continuous_kernelAverage (n : ℕ) (x : E) :
    Continuous (fun B : E →L[ℂ] F => birkhoffAverage ℂ (kernelContraction B) id n x) := by
  have hit : ∀ j, Continuous (fun B : E →L[ℂ] F => (kernelContraction B)^[j] x) := by
    intro j
    induction j with
    | zero => simpa using (continuous_const : Continuous (fun _ : E →L[ℂ] F => x))
    | succ j ih =>
      simpa only [Function.iterate_succ_apply'] using continuous_kernelContraction.clm_apply ih
  unfold birkhoffAverage birkhoffSum
  exact (continuous_finsetSum _ (fun j _ => hit j)).const_smul _

section Measurability

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (E →L[ℂ] F)] [BorelSpace (E →L[ℂ] F)]
  {Ω : Type*} [MeasurableSpace Ω]

/-- Pointwise limits of the continuous approximants give measurable kernel
projections even where the dimension of the kernel changes. -/
theorem measurable_kernelProjection_apply {B : Ω → E →L[ℂ] F}
    (hB : Measurable B) (x : E) : Measurable (fun ω => kernelProjection (B ω) x) := by
  apply measurable_of_tendsto_metrizable
    (fun n => (continuous_kernelAverage n x).measurable.comp hB)
  exact tendsto_pi_nhds.mpr (fun ω => kernelProjection_tendsto (B ω) x)

end Measurability
end Singularity
