import Singularity.FullIdealBoundary
import Singularity.HyperbolicQuasiconvex
import Singularity.AxisTriangleExcess

/-!
# Full-boundary quasiconvex sets are uniformly dense

Opposite ideal approaches produce a bounded-excess triangle around any chosen
point. The explicit axis-segment estimate and quasiconvexity then put the point
within a uniform distance of the set. For an orbit this supplies a compact
cover of the quotient, with no discreteness assumption.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Quasiconvexity extends from exact segment points to bounded-excess triples. -/
theorem HyperbolicQuasiconvex.near_of_excess {S : Set ℍ} {D : ℝ}
    (hS : HyperbolicQuasiconvex S D) (x : ℍ) (hxS : x ∈ S) (y : ℍ) (hyS : y ∈ S)
    (o : ℍ) (E : ℝ) (he : dist x o + dist y o - dist x y ≤ E) :
    ∃ v ∈ S, dist o v ≤ E / 2 + Real.log 4 + D := by
  obtain ⟨g, u, hx, hy, hu, hd⟩ := exists_axis_point_of_triangle_excess x o y E he
  let w := g • verticalHeightRay UpperHalfPlane.I u
  have h1 : dist x w = u := by
    calc
      _ = dist (g • UpperHalfPlane.I) (g • verticalHeightRay UpperHalfPlane.I u) := by rw [hx]
      _ = u := by rw [dist_smul, verticalHeightRay_dist UpperHalfPlane.I hu.1]
  have h2 : dist w y = dist x y - u := by
    calc
      _ = dist (g • verticalHeightRay UpperHalfPlane.I u)
          (g • verticalHeightRay UpperHalfPlane.I (dist x y)) := by rw [hy]
      _ = dist x y - u := by
        rw [dist_smul, verticalHeightRay_dist_eq, abs_of_nonpos (sub_nonpos.mpr hu.2)]
        ring
  have hw : dist x w + dist w y = dist x y := by rw [h1, h2]; ring
  obtain ⟨v, hv, hclose⟩ := hS x hxS y hyS w hw
  refine ⟨v, hv, ?_⟩
  have ht := dist_triangle o w v
  have hd' : dist o w ≤ E / 2 + Real.log 4 := by simpa only [dist_comm] using hd
  linarith

/-- A full-boundary quasiconvex set is uniformly near i. -/
theorem HyperbolicQuasiconvex.near_I_of_full_boundary {S : Set ℍ} {D : ℝ}
    (hS : HyperbolicQuasiconvex S D) (hfull : HasFullIdealBoundary S) :
    ∃ v ∈ S, dist UpperHalfPlane.I v ≤ D + 2 * Real.log 4 := by
  obtain ⟨x, hx, y, hy, he⟩ := hfull.exists_bounded_excess
  obtain ⟨v, hv, hd⟩ := hS.near_of_excess x hx y hy UpperHalfPlane.I (2 * Real.log 4) he
  exact ⟨v, hv, by linarith⟩

/-- Every point is within a fixed distance of a full-boundary quasiconvex set. -/
theorem HyperbolicQuasiconvex.uniform_cover_of_full_boundary {S : Set ℍ} {D : ℝ}
    (hS : HyperbolicQuasiconvex S D) (hfull : HasFullIdealBoundary S) :
    ∀ w : ℍ, ∃ v ∈ S, dist w v ≤ D + 2 * Real.log 4 := by
  intro w
  let B := w.toSL2R
  obtain ⟨_, ⟨v, hv, rfl⟩, hd⟩ := (hS.smul_image B⁻¹).near_I_of_full_boundary (hfull.smul_image B⁻¹)
  refine ⟨v, hv, ?_⟩
  rw [← dist_smul B UpperHalfPlane.I (B⁻¹ • v), smul_inv_smul] at hd
  simpa only [B, UpperHalfPlane.toSL2R_smul_I] using hd

/-- A uniform bound from the whole plane to one projective orbit gives a
compact quotient. The covering set is a single closed hyperbolic ball. -/
theorem projective_cocompact_of_uniform_orbit_cover (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (R : ℝ)
    (hcover : ∀ w : ℍ, ∃ g : Γ, dist w (g • z) ≤ R) :
    CompactSpace (Quotient (MulAction.orbitRel Γ ℍ)) := by
  let π : ℍ → Quotient (MulAction.orbitRel Γ ℍ) := Quotient.mk _
  have hπ : Continuous π := continuous_quotient_mk'
  have hsurj : π '' Metric.closedBall z R = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h w =>
      obtain ⟨g, hg⟩ := hcover w
      refine ⟨g⁻¹ • w, ?_, ?_⟩
      · change dist (g⁻¹ • w) z ≤ R
        have he : dist (g⁻¹ • w) z = dist w (g • z) := by
          have hh := projective_dist_smul (g : PSL(2, ℝ)) (g⁻¹ • w) z
          change dist (g • (g⁻¹ • w)) (g • z) = dist (g⁻¹ • w) z at hh
          simpa only [smul_inv_smul] using hh.symm
        rwa [he]
      · exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g⁻¹, rfl⟩)
  exact isCompact_univ_iff.mp (hsurj ▸ (isCompact_closedBall z R).image hπ)

/-- A quasiconvex projective orbit with full limit set has compact quotient. -/
theorem projective_cocompact_of_quasiconvex_full_limitSet (Γ : Subgroup PSL(2, ℝ))
    (z : ℍ) (D : ℝ) (hqc : HyperbolicQuasiconvex (MulAction.orbit Γ z) D)
    (hfull : projectiveOrbitLimitSet Γ z = Set.univ) :
    CompactSpace (Quotient (MulAction.orbitRel Γ ℍ)) := by
  have hf := (full_projectiveOrbitLimitSet_iff Γ z).mp hfull
  apply projective_cocompact_of_uniform_orbit_cover Γ z (D + 2 * Real.log 4)
  intro w
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := hqc.uniform_cover_of_full_boundary hf w
  exact ⟨g, hg⟩

end Singularity
