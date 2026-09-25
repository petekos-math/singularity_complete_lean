import Singularity.DilationGeometry
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction

/-!
# Compact normalization of a dilation-invariant strip

We use the coordinate strip |re(z)/im(z)| ≤ R. Normalizing height by a power
of the diagonal element places this strip in a compact rectangle. Proper
discontinuity then makes the corresponding set of group vertices finite,
including all vertices with the same orbit point.
-/

noncomputable section
open Set
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- A dilation-invariant strip around the vertical axis. -/
def axisRatioStrip (R : ℝ) : Set ℍ := {z | |z.re / z.im| ≤ R}

/-- A closed rectangle in the upper half plane, bounded away from height zero. -/
def heightRectangle (C H : ℝ) : Set ℍ := {z | |z.re| ≤ C ∧ 1 ≤ z.im ∧ z.im ≤ H}

/-- A rectangle bounded away from the real boundary is compact in ℍ. -/
theorem isCompact_heightRectangle (C H : ℝ) : IsCompact (heightRectangle C H) := by
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff (f := ((↑) : ℍ → ℂ))]
  have he : ((↑) : ℍ → ℂ) '' heightRectangle C H = Icc (-C) C ×ℂ Icc 1 H := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨abs_le.mp hz.1, hz.2⟩
    · rintro ⟨hre, him⟩
      refine ⟨⟨w, lt_of_lt_of_le zero_lt_one him.1⟩, ?_, rfl⟩
      exact ⟨abs_le.mpr hre, him⟩
  rw [he]
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- All integer dilations preserve the coordinate strip. -/
theorem dilationMatrix_zpow_mem_axisRatioStrip (R τ : ℝ) (n : ℤ) (z : ℍ) :
    dilationMatrix τ ^ n • z ∈ axisRatioStrip R ↔ z ∈ axisRatioStrip R := by
  rw [← dilationMatrix_zpow]
  change |(dilationMatrix _ • z).re / (dilationMatrix _ • z).im| ≤ R ↔ _
  rw [dilationMatrix_smul_ratio]
  rfl

/-- The normalized part of the strip is contained in a compact rectangle. -/
theorem axisRatioStrip_height_subset {R τ : ℝ} (hR : 0 ≤ R) (z : ℍ)
    (hz : z ∈ axisRatioStrip R) (hlo : 1 ≤ z.im) (hhi : z.im ≤ Real.exp τ) :
    z ∈ heightRectangle (R * Real.exp τ) (Real.exp τ) := by
  refine ⟨?_, hlo, hhi⟩
  have hr : |z.re| ≤ R * z.im := by
    change |z.re / z.im| ≤ R at hz
    rw [abs_div, abs_of_pos z.im_pos] at hz
    exact (div_le_iff₀ z.im_pos).mp hz
  exact hr.trans (mul_le_mul_of_nonneg_left hhi hR)

/-- Every strip point can be moved into the fixed compact height rectangle. -/
theorem exists_dilationMatrix_mem_heightRectangle {R τ : ℝ} (hR : 0 ≤ R) (hτ : 0 < τ)
    (z : ℍ) (hz : z ∈ axisRatioStrip R) :
    ∃ n : ℤ, dilationMatrix τ ^ n • z ∈ heightRectangle (R * Real.exp τ) (Real.exp τ) := by
  obtain ⟨n, hlo, hhi⟩ := exists_dilationMatrix_height_band hτ z
  exact ⟨n, axisRatioStrip_height_subset hR _
    ((dilationMatrix_zpow_mem_axisRatioStrip R τ n z).mpr hz) hlo hhi.le⟩

/-- A half-open height band contains at most one point of each dilation orbit. -/
theorem dilationMatrix_height_band_unique {τ : ℝ} (hτ : 0 < τ) (z : ℍ)
    (hlo : 1 ≤ z.im) (hhi : z.im < Real.exp τ) (n : ℤ)
    (hnlo : 1 ≤ (dilationMatrix τ ^ n • z).im)
    (hnhi : (dilationMatrix τ ^ n • z).im < Real.exp τ) : n = 0 := by
  have hl₀ := Real.log_nonneg hlo
  have hl₁ := (Real.log_lt_iff_lt_exp z.im_pos).mpr hhi
  have hn₀ := Real.log_nonneg hnlo
  have hn₁ := (Real.log_lt_iff_lt_exp (dilationMatrix τ ^ n • z).im_pos).mpr hnhi
  rw [← dilationMatrix_zpow, dilationMatrix_smul_im,
    Real.log_mul (Real.exp_ne_zero _) z.im_pos.ne', Real.log_exp] at hn₀ hn₁
  have hlt : (n : ℝ) < 1 := by nlinarith
  have hgt : (-1 : ℝ) < (n : ℝ) := by nlinarith
  have hlt' : n < 1 := by exact_mod_cast hlt
  have hgt' : -1 < n := by exact_mod_cast hgt
  omega

/-- Proper discontinuity bounds group vertices, not just distinct orbit points. -/
theorem finite_group_vertices_in_compact (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (z : ℍ) {K : Set ℍ} (hK : IsCompact K) : {g : Γ | g • z ∈ K}.Finite := by
  have hf := finite_disjoint_inter_image (Γ := Γ) (K := {z}) (L := K) isCompact_singleton hK
  apply hf.subset
  intro g hg
  exact ⟨g • z, ⟨z, mem_singleton z, rfl⟩, hg⟩

/-- Canonical group representatives use a half-open fundamental height band. -/
def stripRepresentatives (Γ : Subgroup SL(2, ℝ)) (z : ℍ) (R τ : ℝ) : Set Γ :=
  {g | g • z ∈ axisRatioStrip R ∧ 1 ≤ (g • z).im ∧ (g • z).im < Real.exp τ}

/-- The representative set is finite for every discrete subgroup. -/
theorem finite_stripRepresentatives (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (z : ℍ) {R : ℝ} (hR : 0 ≤ R) (τ : ℝ) : (stripRepresentatives Γ z R τ).Finite := by
  apply (finite_group_vertices_in_compact Γ z
    (isCompact_heightRectangle (R * Real.exp τ) (Real.exp τ))).subset
  intro g hg
  exact axisRatioStrip_height_subset hR _ hg.1 hg.2.1 hg.2.2.le

/-- The point of the vertical axis at the same height as z. -/
def verticalAxisPoint (z : ℍ) : ℍ := ⟨⟨0, z.im⟩, z.im_pos⟩

/-- The coordinate strip lies within a uniformly bounded distance of the axis. -/
theorem axisRatioStrip_dist_to_axis_le {R : ℝ} (z : ℍ) (hz : z ∈ axisRatioStrip R) :
    dist z (verticalAxisPoint z) ≤ 2 * Real.arsinh (R / 2) := by
  have he : (z : ℂ) - (verticalAxisPoint z : ℂ) = (z.re : ℂ) := by
    apply Complex.ext <;> simp [verticalAxisPoint]
  have hd : dist (z : ℂ) (verticalAxisPoint z : ℂ) = |z.re| := by
    rw [dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs]
  rw [UpperHalfPlane.dist_le_iff_le_sinh, hd]
  change |z.re| / (2 * Real.sqrt (z.im * z.im)) ≤ Real.sinh (2 * Real.arsinh (R / 2) / 2)
  rw [Real.sqrt_mul_self z.im_pos.le, mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0),
    Real.sinh_arsinh]
  change |z.re / z.im| ≤ R at hz
  rw [abs_div, abs_of_pos z.im_pos] at hz
  have hi : |z.re| / (2 * z.im) = (|z.re| / z.im) / 2 := by ring
  rw [hi]
  exact div_le_div_of_nonneg_right hz (by norm_num)

/-- In particular this coordinate region is a genuine bounded-width axis strip. -/
theorem axisRatioStrip_bounded_width {R : ℝ} (z : ℍ) (hz : z ∈ axisRatioStrip R) :
    ∃ w : ℍ, w.re = 0 ∧ dist z w ≤ 2 * Real.arsinh (R / 2) :=
  ⟨verticalAxisPoint z, rfl, axisRatioStrip_dist_to_axis_le z hz⟩

end Singularity
