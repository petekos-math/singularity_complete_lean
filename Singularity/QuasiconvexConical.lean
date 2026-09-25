import Singularity.VerticalRayExcess
import Singularity.VisualPoissonOrbit

/-!
# Quasiconvex orbits track vertical approaches to every finite ideal limit point

The approach ξ+i exp(-t) becomes the upward vertical ray under the explicit
pole matrix. Applying the checked segment-excess estimate gives nearby orbit
points with one uniform distance bound. This supplies the geometric input for
a density-point/Poisson concentration argument.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- Vertical Euclidean approach to a finite ideal point. -/
def finiteVerticalApproach (ξ t : ℝ) : ℍ := ⟨⟨ξ, Real.exp (-t)⟩, Real.exp_pos _⟩

/-- The pole matrix sends this approach to the upward unit-speed ray from i. -/
theorem boundaryPoleMatrix_verticalApproach (ξ t : ℝ) :
    boundaryPoleMatrix ξ • finiteVerticalApproach ξ t = verticalHeightRay UpperHalfPlane.I t := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [boundaryPoleMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, RingHom.id_apply, Algebra.algebraMap_self, Complex.ofReal_zero,
    Complex.ofReal_one, Complex.ofReal_neg, zero_mul, zero_add, one_mul]
  change (-1 : ℂ) / ((⟨ξ, Real.exp (-t)⟩ : ℂ) - (ξ : ℂ)) = ⟨0, Real.exp t * 1⟩
  have hd : (⟨ξ, Real.exp (-t)⟩ : ℂ) - (ξ : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
    exact (Real.exp_ne_zero _) hi
  rw [div_eq_iff hd]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Real.exp_neg]

/-- The finite endpoint is mapped to infinity by the same normalization. -/
theorem boundaryPoleMatrix_smul_endpoint (ξ : ℝ) :
    boundaryPoleMatrix ξ • (ξ : OnePoint ℝ) = ∞ := by
  apply compactBoundary_smul_pole
  simp [boundaryPoleMatrix]

/-- Every finite limit point of a quasiconvex orbit has a vertical approach
uniformly close to that orbit. -/
theorem quasiconvex_orbit_tracks_finite_limitPoint (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    (D : ℝ) (hqc : HyperbolicQuasiconvex (MulAction.orbit Γ z) D)
    (ξ : ℝ) (hξ : (ξ : OnePoint ℝ) ∈ projectiveOrbitLimitSet Γ z) :
    ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t → ∃ g : Γ, dist (finiteVerticalApproach ξ t) (g • z) ≤ R := by
  obtain ⟨x, hx⟩ := (mem_projectiveOrbitLimitSet_iff_sequence Γ z ξ).mp hξ
  let B := boundaryPoleMatrix ξ
  let S := (fun w : ℍ => B • w) '' MulAction.orbit Γ z
  have hS : HyperbolicQuasiconvex S D := hqc.smul_image B
  have hlim : Tendsto (fun n => hyperbolicCompactEmbedding (B • (x n • z))) atTop
      (𝓝 (∞ : OnePoint ℂ)) := by
    have ht := (continuous_const_smul B).continuousAt.tendsto.comp hx
    have hb : B • compactBoundaryEmbedding (ξ : OnePoint ℝ) = (∞ : OnePoint ℂ) := by
      rw [← compactBoundaryEmbedding_smul, boundaryPoleMatrix_smul_endpoint]
      rfl
    simpa only [Function.comp_def, hyperbolicCompactEmbedding_smul, hb] using ht
  refine ⟨D + dist (B • z) UpperHalfPlane.I + (3 / 2 : ℝ) * Real.log 4, fun t ht => ?_⟩
  have ha : B • z ∈ S := ⟨z, ⟨1, one_smul Γ z⟩, rfl⟩
  have hxS (n : ℕ) : B • (x n • z) ∈ S := ⟨x n • z, ⟨x n, rfl⟩, rfl⟩
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hg⟩ :=
    hS.near_verticalRay (B • z) ha (fun n => B • (x n • z)) hxS hlim t ht
  refine ⟨g, ?_⟩
  rw [← dist_smul B (finiteVerticalApproach ξ t) (g • z), boundaryPoleMatrix_verticalApproach]
  exact hg

/-- Poisson concentration at any finite ideal limit point of a quasiconvex
orbit forces the entire ideal boundary. The analytic concentration premise
is explicit here. -/
theorem full_limitSet_of_quasiconvex_poisson_concentration (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    (D : ℝ) (hqc : HyperbolicQuasiconvex (MulAction.orbit Γ z) D)
    (ξ : ℝ) (hξ : (ξ : OnePoint ℝ) ∈ projectiveOrbitLimitSet Γ z)
    (hlim : Tendsto (fun n : ℕ => compactPoissonMeasure (finiteVerticalApproach ξ n)
      (projectiveOrbitLimitSet Γ z)ᶜ) atTop (𝓝 0)) :
    projectiveOrbitLimitSet Γ z = Set.univ := by
  obtain ⟨R, hR⟩ := quasiconvex_orbit_tracks_finite_limitPoint Γ z D hqc ξ hξ
  exact full_limitSet_of_visual_concentration_near_orbit Γ z
    (fun n : ℕ => finiteVerticalApproach ξ n) R (fun n => hR n (Nat.cast_nonneg n)) hlim

end Singularity
