import Singularity.VisualPoissonRay
import Singularity.OrbitGreenBoundary

/-!
# Uniform decay of visual Poisson kernels along cyclic orbits

At each fixed nonzero finite boundary coordinate, visual Poisson kernels along
integer dilations admit an explicit exponential envelope. Its square is summable
on every finite family of cyclic orbits.
-/

noncomputable section
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- A scalar estimate for the two tails of a dilated Poisson expression. -/
theorem exp_scaled_ratio_decay {ξ : ℝ} (hξ : ξ ≠ 0) (t : ℝ) :
    Real.exp (-t) / (1 + (Real.exp (-t) * ξ) ^ 2) ≤
      (1 + (ξ⁻¹) ^ 2) * Real.exp (-|t|) := by
  have hi : (ξ⁻¹) ^ 2 * ξ ^ 2 = 1 := by field_simp
  have hd : 1 + (Real.exp (-t)) ^ 2 ≤
      (1 + (ξ⁻¹) ^ 2) * (1 + (Real.exp (-t) * ξ) ^ 2) := by
    have he := congrArg (fun a : ℝ => (Real.exp (-t)) ^ 2 * a) hi
    nlinarith [sq_nonneg (ξ⁻¹), mul_nonneg (sq_nonneg (Real.exp (-t))) (sq_nonneg ξ)]
  calc
    Real.exp (-t) / (1 + (Real.exp (-t) * ξ) ^ 2) ≤
        (1 + (ξ⁻¹) ^ 2) * (Real.exp (-t) / (1 + (Real.exp (-t)) ^ 2)) := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hd (Real.exp_pos (-t)).le]
    _ ≤ (1 + (ξ⁻¹) ^ 2) * Real.exp (-|-t|) :=
      mul_le_mul_of_nonneg_left (exp_ratio_le_exp_neg_abs (-t)) (by positivity)
    _ = (1 + (ξ⁻¹) ^ 2) * Real.exp (-|t|) := by rw [abs_neg]

/-- An explicit envelope constant, depending only on the point and boundary coordinate. -/
def visualPoissonEnvelope (z : ℍ) (ξ : ℝ) : ℝ :=
  (Real.pi * (1 + ξ ^ 2)) * poissonEnvelopeConstant z.re z.im * (1 + (ξ⁻¹) ^ 2)

theorem visualPoissonEnvelope_pos (z : ℍ) (ξ : ℝ) : 0 < visualPoissonEnvelope z ξ := by
  unfold visualPoissonEnvelope
  have hc := poissonEnvelopeConstant_pos z.re z.im_pos
  positivity

/-- The visual kernel decays in both directions along the full dilation subgroup. -/
theorem visualPoisson_dilation_decay (z : ℍ) {ξ : ℝ} (hξ : ξ ≠ 0) (t : ℝ) :
    visualPoisson (dilationMatrix t • z) ξ ≤ visualPoissonEnvelope z ξ * Real.exp (-|t|) := by
  rw [visualPoisson_eq_density, dilationMatrix_smul_re, dilationMatrix_smul_im,
    ← halfPlanePoisson_dilation]
  change (Real.pi * (1 + ξ ^ 2)) *
    (Real.exp (-t) * halfPlanePoisson z.re z.im (Real.exp (-t) * ξ)) ≤ _
  calc
    _ ≤ (Real.pi * (1 + ξ ^ 2)) * (Real.exp (-t) *
        (poissonEnvelopeConstant z.re z.im / (1 + (Real.exp (-t) * ξ) ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (halfPlanePoisson_le z.re z.im_pos _) (Real.exp_pos _).le)
        (by positivity)
    _ = ((Real.pi * (1 + ξ ^ 2)) * poissonEnvelopeConstant z.re z.im) *
        (Real.exp (-t) / (1 + (Real.exp (-t) * ξ) ^ 2)) := by ring
    _ ≤ ((Real.pi * (1 + ξ ^ 2)) * poissonEnvelopeConstant z.re z.im) *
        ((1 + (ξ⁻¹) ^ 2) * Real.exp (-|t|)) :=
      mul_le_mul_of_nonneg_left (exp_scaled_ratio_decay hξ t)
        (mul_nonneg (by positivity) (poissonEnvelopeConstant_pos z.re z.im_pos).le)
    _ = visualPoissonEnvelope z ξ * Real.exp (-|t|) := by
      unfold visualPoissonEnvelope
      ring

/-- The decay rate on integer orbits is exactly the positive dilation parameter. -/
theorem visualPoisson_zpow_decay (z : ℍ) {ξ τ : ℝ} (hξ : ξ ≠ 0) (hτ : 0 < τ) (n : ℤ) :
    visualPoisson (dilationMatrix τ ^ n • z) ξ ≤
      visualPoissonEnvelope z ξ * Real.exp (-τ * |(n : ℝ)|) := by
  rw [← dilationMatrix_zpow]
  have h := visualPoisson_dilation_decay z hξ ((n : ℝ) * τ)
  rw [abs_mul, abs_of_pos hτ] at h
  have he : -(|(n : ℝ)| * τ) = -τ * |(n : ℝ)| := by ring
  rwa [he] at h

/-- The actual visual kernels, not just their envelopes, are square-summable. -/
theorem summable_visualPoisson_orbits_sq {J : Type*} [Fintype J] (z : J → ℍ)
    {ξ τ : ℝ} (hξ : ξ ≠ 0) (hτ : 0 < τ) :
    Summable (fun p : ℤ × J => (visualPoisson (dilationMatrix τ ^ p.1 • z p.2) ξ) ^ 2) := by
  apply (summable_orbit_exp_sq hτ (fun j => visualPoissonEnvelope (z j) ξ)).of_nonneg_of_le
  · intro p
    exact sq_nonneg _
  · intro p
    exact pow_le_pow_left₀ (visualPoisson_pos _ _).le
      (visualPoisson_zpow_decay (z p.2) hξ hτ p.1) 2

end Singularity
