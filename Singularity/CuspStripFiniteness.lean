import Singularity.ParabolicOrbitHeight
import Singularity.GeometricStrip
import Singularity.VisualPoissonRay
import Singularity.ConjugateSubgroup

/-!
# A strip between two height-controlled ideal endpoints is finite

Upper bounds for height at infinity and at zero keep an axis-ratio strip
away from both ideal endpoints. It lies in a compact rectangle, so a discrete
orbit contributes only finitely many group vertices. This supplies an actual
finite separator when both endpoint height bounds are available.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- A closed rectangle with any positive lower height is compact in H². -/
theorem isCompact_heightBandRectangle (C l H : ℝ) (hl : 0 < l) :
    IsCompact {z : ℍ | |z.re| ≤ C ∧ l ≤ z.im ∧ z.im ≤ H} := by
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff (f := ((↑) : ℍ → ℂ))]
  have he : ((↑) : ℍ → ℂ) '' {z : ℍ | |z.re| ≤ C ∧ l ≤ z.im ∧ z.im ≤ H} =
      Icc (-C) C ×ℂ Icc l H := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨abs_le.mp hz.1, hz.2⟩
    · rintro ⟨hre, him⟩
      exact ⟨⟨w, hl.trans_le him.1⟩, ⟨abs_le.mpr hre, him⟩, rfl⟩
  rw [he]
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- A pole-height bound at zero gives a positive lower height in a fixed
axis-ratio strip. -/
theorem axisRatioStrip_height_lower_of_pole_bound {R D : ℝ} (hD : 0 < D)
    (z : ℍ) (hz : z ∈ axisRatioStrip R) (hpole : (boundaryPoleMatrix 0 • z).im ≤ D) :
    1 / (D * (R ^ 2 + 1)) ≤ z.im := by
  have hr : |z.re| ≤ R * z.im := by
    change |z.re / z.im| ≤ R at hz
    rw [abs_div, abs_of_pos z.im_pos] at hz
    exact (div_le_iff₀ z.im_pos).mp hz
  have hsq : z.re ^ 2 ≤ R ^ 2 * z.im ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg z.re) hr 2
    simpa only [sq_abs, mul_pow] using h
  have hden : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  rw [boundaryPoleMatrix_smul_im] at hpole
  simp only [zero_sub, neg_sq] at hpole
  have hp := (div_le_iff₀ hden).mp hpole
  have hs := mul_le_mul_of_nonneg_left hsq hD.le
  have hmul : 1 * z.im ≤ (D * (R ^ 2 + 1) * z.im) * z.im := by nlinarith
  have hone := (mul_le_mul_iff_of_pos_right z.im_pos).mp hmul
  apply (div_le_iff₀ (mul_pos hD (by positivity : 0 < R ^ 2 + 1))).mpr
  nlinarith

/-- Two endpoint height bounds make every fixed axis strip contain only
finitely many vertices of a discrete subgroup. -/
theorem finite_axisRatioStrip_of_two_height_bounds
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ)
    {R C D : ℝ} (hR : 0 ≤ R) (hD : 0 < D)
    (hinfty : ∀ g : Γ, (g • z).im ≤ C)
    (hzero : ∀ g : Γ, (boundaryPoleMatrix 0 • (g • z)).im ≤ D) :
    {g : Γ | g • z ∈ axisRatioStrip R}.Finite := by
  let l := 1 / (D * (R ^ 2 + 1))
  have hl : 0 < l := by dsimp [l]; positivity
  apply (finite_group_vertices_in_compact Γ z (isCompact_heightBandRectangle (R * C) l C hl)).subset
  intro g hg
  refine ⟨?_, axisRatioStrip_height_lower_of_pole_bound hD _ hg (hzero g), hinfty g⟩
  have hr : |(g • z).re| ≤ R * (g • z).im := by
    change |(g • z).re / (g • z).im| ≤ R at hg
    rw [abs_div, abs_of_pos (g • z).im_pos] at hg
    exact (div_le_iff₀ (g • z).im_pos).mp hg
  exact hr.trans (mul_le_mul_of_nonneg_left (hinfty g) hR)

/-- With two controlled endpoints, the already constructed finite-jump
separator is genuinely finite, rather than merely periodic. -/
theorem finite_finiteJumpStrip_of_two_height_bounds
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (s : Finset Γ)
    {C D : ℝ} (hD : 0 < D)
    (hinfty : ∀ g : Γ, (g • z).im ≤ C)
    (hzero : ∀ g : Γ, (boundaryPoleMatrix 0 • (g • z)).im ≤ D) :
    (finiteJumpStrip Γ z s).Finite :=
  finite_axisRatioStrip_of_two_height_bounds Γ z
    (jumpStripRadius_pos (finiteJumpLengthBound_nonneg Γ z s)).le hD hinfty hzero

/-- Nontrivial parabolic shears at both endpoints supply the two height
bounds internally. Hence every fixed axis-ratio strip between them is finite. -/
theorem finite_axisRatioStrip_of_two_parabolic_shears
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) {R : ℝ} (hR : 0 ≤ R)
    (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hinfty : upperShearMatrix u ∈ Γ)
    (hzero : (boundaryPoleMatrix 0)⁻¹ * upperShearMatrix v * boundaryPoleMatrix 0 ∈ Γ) :
    {g : Γ | g • z ∈ axisRatioStrip R}.Finite := by
  obtain ⟨C, _, hC⟩ := discrete_upperShear_orbit_height_bound Γ u hu hinfty z
  let J := boundaryPoleMatrix 0
  let Λ := conjugateSubgroup Γ J⁻¹
  let : DiscreteTopology Λ := conjugateSubgroup_discrete Γ J⁻¹
  have hvΛ : upperShearMatrix v ∈ Λ := by
    change J⁻¹ * upperShearMatrix v * (J⁻¹)⁻¹ ∈ Γ
    simpa only [inv_inv] using hzero
  obtain ⟨D, hD, hΛ⟩ := discrete_upperShear_orbit_height_bound Λ v hv hvΛ (J • z)
  apply finite_axisRatioStrip_of_two_height_bounds Γ z hR hD hC
  intro g
  let a : Λ := (conjugateSubgroupEquiv Γ J⁻¹).symm g
  have he : a • (J • z) = J • (g • z) := by
    have hh := congrArg (fun w : ℍ => J • w)
      (conjugateSubgroup_hyperbolic_action Γ J⁻¹ a (J • z))
    simpa only [smul_inv_smul, inv_smul_smul, a, MulEquiv.apply_symm_apply] using hh
  simpa only [he] using hΛ a

/-- Nontrivial parabolic shears at both endpoints supply the two height
bounds internally. Hence the finite-jump separator between them is finite. -/
theorem finite_finiteJumpStrip_of_two_parabolic_shears
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (s : Finset Γ)
    (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hinfty : upperShearMatrix u ∈ Γ)
    (hzero : (boundaryPoleMatrix 0)⁻¹ * upperShearMatrix v * boundaryPoleMatrix 0 ∈ Γ) :
    (finiteJumpStrip Γ z s).Finite :=
  finite_axisRatioStrip_of_two_parabolic_shears Γ z
    (jumpStripRadius_pos (finiteJumpLengthBound_nonneg Γ z s)).le u v hu hv hinfty hzero

end Singularity
