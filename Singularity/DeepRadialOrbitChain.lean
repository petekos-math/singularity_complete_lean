import Singularity.AxisOrbitChain
import Singularity.RadialGeodesicConvexity

/-!
# Orbit chains between arbitrary deep endpoints

The constructed geodesic remains above the common radial level of its ends.
Approximating it by the orbit loses only the fixed covering radius in depth.
There is no restriction that either endpoint lie near the original chart axis.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Short orbit chains join all endpoints above a radial level, losing at most
the covering radius in depth and retaining the prescribed endpoint vertices. -/
theorem deep_radial_orbit_chain_of_cover (Γ : Subgroup SL(2, ℝ)) (E : ℝ) (hE : 0 ≤ E)
    (hcover : ∀ z : ℍ, ∃ g : Γ, dist (g • UpperHalfPlane.I) z ≤ E)
    (q : SL(2, ℝ)) (r : ℝ) (x y : Γ)
    (hx : r ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)))
    (hy : r ≤ axisRadialCoordinate (q • (y • UpperHalfPlane.I))) :
    ∃ (N : ℕ) (f : ℕ → Γ), f 0 = x ∧ f N = y ∧
      (N : ℝ) ≤ dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)+4 ∧
      (∀ k < N, dist (f k • UpperHalfPlane.I) (f (k+1) • UpperHalfPlane.I) ≤ 2*E+1) ∧
      ∀ k ≤ N, r-E ≤ axisRadialCoordinate (q • (f k • UpperHalfPlane.I)) := by
  let d := dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)
  obtain ⟨g,hg0,hgd⟩ := exists_oriented_hyperbolic_axis (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)
  have hstart : dist (g⁻¹ • (x • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I 0) ≤ E := by
    rw [← hg0, inv_smul_smul, verticalHeightRay_zero, dist_self]
    exact hE
  have hend : dist (g⁻¹ • (y • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I d) ≤ E := by
    rw [← hgd, inv_smul_smul, dist_self]
    exact hE
  obtain ⟨N,f,hf0,hfN,hN,hstep,htube⟩ := axis_orbit_chain_with_tube Γ E hE hcover g⁻¹ 0 d
    dist_nonneg x y hstart hend
  refine ⟨N,f,hf0,hfN,by simpa only [sub_zero] using hN,hstep,?_⟩
  intro k hk
  obtain ⟨t,ht,hclose⟩ := htube k hk
  have hsegment : r ≤ axisRadialCoordinate (q • (g • verticalHeightRay UpperHalfPlane.I t)) := by
    rw [← mul_smul]
    apply axisRadialCoordinate_segment_lower (q*g) r 0 d t ht.1 ht.2
    · simpa only [mul_smul, verticalHeightRay_zero, hg0] using hx
    · simpa only [d, mul_smul, hgd] using hy
  have hd : dist (q • (f k • UpperHalfPlane.I))
      (q • (g • verticalHeightRay UpperHalfPlane.I t)) ≤ E := by
    rw [dist_smul]
    rw [← dist_smul g] at hclose
    simpa only [smul_inv_smul] using hclose
  have hh := abs_le.mp ((axisRadialCoordinate_dist_le _ _).trans hd)
  linarith [hh.1]

end Singularity
