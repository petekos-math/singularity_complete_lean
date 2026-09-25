import Singularity.ParabolicMidpoint
import Singularity.ConjugateSubgroup
import Singularity.ProjectiveSubgroupLift

/-!
# Quasiconvex subsets and parabolic orbit segments

Quasiconvexity means that every point on every metric segment with endpoints
in the set is within a fixed distance of the set. The definition is transported
under ambient hyperbolic isometries. A discrete group containing a nontrivial
upper shear cannot have a quasiconvex orbit.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Metric-segment quasiconvexity in the hyperbolic plane. -/
def HyperbolicQuasiconvex (S : Set ℍ) (D : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ w : ℍ, dist x w + dist w y = dist x y →
    ∃ v ∈ S, dist w v ≤ D

/-- Quasiconvexity is preserved by an ambient special-linear isometry. -/
theorem HyperbolicQuasiconvex.smul_image {S : Set ℍ} {D : ℝ}
    (hS : HyperbolicQuasiconvex S D) (B : SL(2, ℝ)) :
    HyperbolicQuasiconvex ((fun z : ℍ => B • z) '' S) D := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ w hw
  have hs : dist x (B⁻¹ • w) + dist (B⁻¹ • w) y = dist x y := by
    rw [← dist_smul B x (B⁻¹ • w), ← dist_smul B (B⁻¹ • w) y, ← dist_smul B x y]
    simpa only [smul_inv_smul] using hw
  obtain ⟨v, hv, hd⟩ := hS x hx y hy (B⁻¹ • w) hs
  refine ⟨B • v, ⟨v, hv, rfl⟩, ?_⟩
  rw [← dist_smul B (B⁻¹ • w) v, smul_inv_smul] at hd
  exact hd

/-- Ambient isometries preserve quasiconvexity in both directions. -/
theorem hyperbolicQuasiconvex_smul_image_iff (S : Set ℍ) (D : ℝ) (B : SL(2, ℝ)) :
    HyperbolicQuasiconvex ((fun z : ℍ => B • z) '' S) D ↔ HyperbolicQuasiconvex S D := by
  constructor
  · intro h
    simpa only [Set.image_image, Function.comp_def, inv_smul_smul, Set.image_id'] using h.smul_image B⁻¹
  · exact fun h => h.smul_image B

/-- The sign lift does not change orbit quasiconvexity. -/
theorem projectiveSubgroupLift_quasiconvex_iff (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (D : ℝ) :
    HyperbolicQuasiconvex (MulAction.orbit (projectiveSubgroupLift Γ) z) D ↔
      HyperbolicQuasiconvex (MulAction.orbit Γ z) D := by
  rw [projectiveSubgroupLift_hyperbolic_orbit]

/-- Inverting an upper shear negates its parameter. -/
theorem upperShearMatrix_inv (t : ℝ) :
    (upperShearMatrix t)⁻¹ = upperShearMatrix (-t) := by
  apply inv_eq_of_mul_eq_one_left
  rw [← upperShearMatrix_add, neg_add_cancel, upperShearMatrix_zero]

/-- A discrete orbit containing the powers of a nontrivial horizontal translation
cannot be quasiconvex. No finite-generation or free-subgroup hypothesis occurs. -/
theorem discrete_upperShear_orbit_not_quasiconvex (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (u : ℝ) (hu : u ≠ 0) (hmem : upperShearMatrix u ∈ Γ) (z : ℍ) :
    ¬∃ D : ℝ, HyperbolicQuasiconvex (MulAction.orbit Γ z) D := by
  obtain ⟨C, hC, hheight⟩ := discrete_upperShear_orbit_height_bound Γ u hu hmem z
  rintro ⟨D, hD⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (C * Real.exp D / |u|)
  have hn' : C * Real.exp D < (n : ℝ) * |u| := (div_lt_iff₀ (abs_pos.mpr hu)).mp hn
  let p : Γ := ⟨upperShearMatrix u, hmem⟩
  have hplus : (p ^ n) • z = upperShearMatrix ((n : ℝ) * u) • z := by
    change (upperShearMatrix u ^ n) • z = _
    rw [upperShearMatrix_pow]
  have hminus : (p ^ n)⁻¹ • z = upperShearMatrix (-((n : ℝ) * u)) • z := by
    change (upperShearMatrix u ^ n)⁻¹ • z = _
    rw [upperShearMatrix_pow, upperShearMatrix_inv]
  let w := parabolicMidpoint z ((n : ℝ) * u)
  have hseg : dist ((p ^ n)⁻¹ • z) w + dist w ((p ^ n) • z) =
      dist ((p ^ n)⁻¹ • z) ((p ^ n) • z) := by
    rw [hplus, hminus]
    exact parabolicMidpoint_on_segment z ((n : ℝ) * u)
  obtain ⟨v, ⟨g, rfl⟩, hv⟩ := hD ((p ^ n)⁻¹ • z) ⟨(p ^ n)⁻¹, rfl⟩
    ((p ^ n) • z) ⟨p ^ n, rfl⟩ w hseg
  have hlow : (n : ℝ) * |u| ≤ w.im := by
    simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using
      abs_le_parabolicMidpoint_im z ((n : ℝ) * u)
  have hupp : w.im ≤ C * Real.exp D := by
    calc
      _ ≤ (g • z).im * Real.exp (dist w (g • z)) := UpperHalfPlane.im_le_im_mul_exp_dist w (g • z)
      _ ≤ C * Real.exp D := mul_le_mul (hheight g) (Real.exp_le_exp.mpr hv)
        (Real.exp_pos _).le hC.le
  exact hn'.not_ge (hlow.trans hupp)

end Singularity
