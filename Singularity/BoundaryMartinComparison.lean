import Singularity.BoundaryRadialChart
import Singularity.RadialGreenComparison
import Singularity.RayMartinConvergence

/-!
# Comparing arbitrary geometric Martin limits with the ray limit

The pole-normalized radial chart supplies the ordinary Ancona comparison for
arbitrary approaches to a finite boundary point. This provides domination by
the already proved minimal ray limit, with no tangential restriction.
-/

noncomputable section
open Filter Set
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- A sequence approaching a real boundary coordinate eventually avoids every
fixed orbit vertex. -/
theorem real_boundary_approach_eventually_ne {α : Type*} {l : Filter α}
    (Γ : Subgroup SL(2, ℝ)) (ξ : ℝ) (y : α → Γ)
    (hy : Tendsto (fun n => ((y n • UpperHalfPlane.I : ℍ) : ℂ)) l (𝓝 (ξ : ℂ))) (g : Γ) :
    ∀ᶠ n in l, g ≠ y n := by
  filter_upwards [(finiteBoundaryRadialChart_tendsto ξ
    (fun n => y n • UpperHalfPlane.I) hy).eventually_ne_atTop
      (axisRadialCoordinate (finiteBoundaryRadialChart ξ • (g • UpperHalfPlane.I)))] with n hn
  intro he
  exact hn (by rw [he])

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hmass hgen hgap in
/-- Every pointwise Martin limit obtained by an arbitrary approach to ξ has
uniform eventual reverse Green comparison along the chosen ray to ξ. -/
theorem real_boundary_martin_eventual_green_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : ℝ) (y : ℕ → Γ) (J : Γ → ℝ),
      Tendsto (fun k => ((y k • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (ξ : ℂ)) →
      (∀ z, Tendsto (fun k => martinQuotient s μ 1 z (y k)) atTop (𝓝 (J z))) →
      ∀ x, ∀ᶠ n in atTop, J x ≤ C *
        (walkGreen s μ x (cocompactRaySequence Γ ξ n) * J (cocompactRaySequence Γ ξ n)) := by
  obtain ⟨C, hC, hb⟩ := cocompact_radial_separated_green_product_bound Γ s μ hpos hmass hgen hgap
    (cocompactOrbitRadius Γ)
  refine ⟨C, hC, ?_⟩
  intro ξ y J hy hJ x
  have hrad := finiteBoundaryRadialChart_tendsto ξ (fun k => y k • UpperHalfPlane.I) hy
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop (axisRadialCoordinate (finiteBoundaryRadialChart ξ • (x • UpperHalfPlane.I)) + Real.log 4)] with n hn
  have ho : dist (finiteBoundaryRadialChart ξ • (cocompactRaySequence Γ ξ n • UpperHalfPlane.I))
      (verticalHeightRay UpperHalfPlane.I n) ≤ cocompactOrbitRadius Γ := by
    rw [← finiteBoundaryRadialChart_ray ξ n, dist_smul]
    exact cocompactRaySequence_bound Γ ξ n
  have he : ∀ᶠ k in atTop, martinQuotient s μ 1 x (y k) ≤
      C * (walkGreen s μ x (cocompactRaySequence Γ ξ n) *
        martinQuotient s μ 1 (cocompactRaySequence Γ ξ n) (y k)) := by
    filter_upwards [hrad.eventually_ge_atTop ((n : ℝ) + Real.log 4)] with k hk
    have hh := hb (finiteBoundaryRadialChart ξ) n x (cocompactRaySequence Γ ξ n) (y k)
      (by linarith) hk ho
    have hd := walkGreen_pos s μ hpos hgen hgap 1 (y k)
    simpa only [martinQuotient, mul_div_assoc] using div_le_div_of_nonneg_right hh hd.le
  exact le_of_tendsto_of_tendsto (hJ x)
    (((hJ (cocompactRaySequence Γ ξ n)).const_mul
      (walkGreen s μ x (cocompactRaySequence Γ ξ n))).const_mul C) he

include hpos hmass hgen hgap in
/-- Any normalized harmonic function with the proved eventual reverse Green
comparison is dominated everywhere by a fixed multiple of the ray limit. -/
theorem harmonic_dominated_by_ray_of_eventual_comparison {ξ : ℝ} {H J : Γ → ℝ}
    (hH : H ∈ rayMartinCluster Γ s μ ξ) (hJ1 : J 1 = 1) (hJp : ∀ x, 0 ≤ J x)
    (hJh : ∀ x, ∑ g ∈ s, μ g * J (x * g) = J x) (C : ℝ) (hC : 0 < C)
    (hb : ∀ x, ∀ᶠ n in atTop, J x ≤ C *
      (walkGreen s μ x (cocompactRaySequence Γ ξ n) * J (cocompactRaySequence Γ ξ n))) :
    ∃ D : ℝ, 0 < D ∧ ∀ x, J x ≤ D * H x := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  have hHprop := rayMartinCluster_harmonic Γ s μ hpos hgen hgap hH
  obtain ⟨A, hA, ha⟩ := cocompact_ray_martin_limit_bounds Γ s μ hpos hmass hgen hgap
  obtain ⟨φ, hφ, hlim⟩ := hH
  let d := walkGreen s μ 1 1
  have hd : 0 < d := walkGreen_pos s μ hpos hgen hgap 1 1
  have hdiag (v : Γ) : walkGreen s μ v v = d := by
    simpa only [mul_one] using walkGreen_left s μ v 1 1
  refine ⟨C * A * d ^ 2, by positivity, ?_⟩
  intro x
  obtain ⟨n, hn⟩ := (hb x).exists
  let v := cocompactRaySequence Γ ξ n
  have hJupper := walkGreen_superharmonic_bound s μ hμ hmass hgap J hJp
    (fun z => (hJh z).le) 1 v
  rw [hdiag, hJ1, mul_one] at hJupper
  have hHlower := (ha ξ H φ hφ hlim n).1
  have hv := walkGreen_pos s μ hpos hgen hgap 1 v
  have hratio : J v ≤ A * d * H v := by
    have hh := (div_le_iff₀ hA).mp hHlower
    have hmul := mul_le_mul_of_nonneg_left hh hd.le
    have hh' : walkGreen s μ 1 v * J v ≤ walkGreen s μ 1 v * (A * d * H v) := by
      nlinarith
    exact (mul_le_mul_iff_right₀ hv).mp hh'
  have hgreen := walkGreen_superharmonic_bound s μ hμ hmass hgap H
    (fun z => (hHprop.2.1 z).le) (fun z => (hHprop.2.2 z).le) x v
  rw [hdiag] at hgreen
  calc
    J x ≤ C * (walkGreen s μ x v * J v) := hn
    _ ≤ C * (walkGreen s μ x v * (A * d * H v)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio
        (walkGreen_nonneg s μ hμ x v)) hC.le
    _ = C * A * d * (walkGreen s μ x v * H v) := by ring
    _ ≤ C * A * d * (d * H x) := mul_le_mul_of_nonneg_left hgreen (by positivity)
    _ = C * A * d ^ 2 * H x := by ring

end Singularity
