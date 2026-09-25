import Singularity.CompactMartinCovariance

/-!
# Minimality of every compact geometric Martin kernel

Normalized translation preserves minimality in the positive harmonic cone.
The finite-chart minimality theorem therefore applies at infinity as well,
and surjectivity identifies the entire abstract Martin boundary as minimal.
-/

noncomputable section
open Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Minimality in the positive harmonic cone is preserved by the normalized
Martin translation action. -/
theorem harmonic_minimal_martinTranslate {Γ : Type*} [Group Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (H : Γ → ℝ) (hHp : ∀ x, 0 < H x)
    (hmin : ∀ f : Γ → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ H x) →
      (∀ x, ∑ a ∈ s, μ a * f (x * a) = f x) →
      ∃ c ∈ Icc (0 : ℝ) 1, ∀ x, f x = c * H x)
    (g : Γ) (f : Γ → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ martinTranslate 1 g H x)
    (hfh : ∀ x, ∑ a ∈ s, μ a * f (x * a) = f x) :
    ∃ c ∈ Icc (0 : ℝ) 1, ∀ x, f x = c * martinTranslate 1 g H x := by
  let d := H g⁻¹
  have hd : 0 < d := hHp g⁻¹
  let F : Γ → ℝ := fun x => d * f (g * x)
  have hF (x : Γ) : 0 ≤ F x ∧ F x ≤ H x := by
    refine ⟨mul_nonneg hd.le (hf (g * x)).1, ?_⟩
    have hh := (hf (g * x)).2
    simp only [martinTranslate, inv_mul_cancel_left, mul_one] at hh
    have hh' := (le_div_iff₀ hd).mp hh
    simpa only [F, mul_comm d] using hh'
  have hFh (x : Γ) : ∑ a ∈ s, μ a * F (x * a) = F x := by
    calc
      _ = d * (∑ a ∈ s, μ a * f ((g * x) * a)) := by
        simp only [F, Finset.mul_sum, mul_assoc, mul_left_comm]
      _ = F x := by rw [hfh]
  obtain ⟨c, hc, hFc⟩ := hmin F hF hFh
  refine ⟨c, hc, fun x => ?_⟩
  have he := hFc (g⁻¹ * x)
  simp only [F, mul_inv_cancel_left] at he
  calc
    f x = (c * H (g⁻¹ * x)) / d := (eq_div_iff (ne_of_gt hd)).mpr (by nlinarith [he])
    _ = c * martinTranslate 1 g H x := by simp only [martinTranslate, mul_one, mul_div_assoc, d]

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

include hmass in
/-- Every compact geometric Martin kernel is minimal, including at infinity. -/
theorem compactMartinPoint_minimal (p : OnePoint ℝ) (f : Γ → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ (compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x)
    (hfh : ∀ x, ∑ a ∈ s, μ a * f (x * a) = f x) :
    ∃ c ∈ Icc (0 : ℝ) 1, ∀ x,
      f x = c * (compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x := by
  obtain ⟨g, ξ, hg⟩ := exists_finite_image_boundary Γ horbit p
  rw [compactMartinPoint_chart Γ s μ hpos hmass hgen hgap horbit p g ξ hg] at hf ⊢
  have hH := rayMartinPoint_mem Γ s μ hpos hgen hgap ξ
  exact harmonic_minimal_martinTranslate s μ _
    (rayMartinCluster_harmonic Γ s μ hpos hgen hgap hH).2.1
    (rayMartinCluster_minimal Γ s μ hpos hmass hgen hgap hH) g⁻¹ f hf hfh

include hpos hmass hgen hgap horbit in
/-- Every point of the actual abstract Martin boundary is minimal. -/
theorem martinBoundary_all_minimal (H : martinBoundary s μ 1) (f : Γ → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ H.val x)
    (hfh : ∀ x, ∑ a ∈ s, μ a * f (x * a) = f x) :
    ∃ c ∈ Icc (0 : ℝ) 1, ∀ x, f x = c * H.val x := by
  obtain ⟨p, rfl⟩ := compactMartinPoint_surjective Γ s μ hpos hmass hgen hgap horbit H
  exact compactMartinPoint_minimal Γ s μ hpos hmass hgen hgap horbit p f hf hfh

end Singularity
