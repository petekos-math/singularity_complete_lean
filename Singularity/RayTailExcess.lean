import Singularity.RayMartinBounds

/-!
# Uniform triangle excess far along a ray

For fixed x, the sequence d(x,r(n))-n is decreasing and bounded below.
Approximation of its infimum gives excess at most one on a sufficiently late
tail. The constant is independent of x; the start of the tail need not be.
-/

noncomputable section
open Filter Set
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- In any metric space, later portions of a geodesic ray have small triangle
excess relative to a fixed point. -/
theorem geodesic_ray_eventual_triangle_excess {X : Type*} [MetricSpace X]
    (r : ℕ → X) (hr : ∀ m n : ℕ, m ≤ n → dist (r m) (r n) = (n : ℝ) - m)
    (x : X) : ∀ᶠ n in atTop, ∀ m, n ≤ m →
      dist x (r n) + dist (r m) (r n) - dist x (r m) ≤ 1 := by
  let a : ℕ → ℝ := fun n => dist x (r n) - n
  have hanti : Antitone a := by
    intro n m hnm
    have hh := dist_triangle x (r n) (r m)
    rw [hr n m hnm] at hh
    dsimp only [a]
    linarith
  have hb : BddBelow (range a) := by
    refine ⟨-dist x (r 0), ?_⟩
    rintro _ ⟨n, rfl⟩
    have hh := dist_triangle (r 0) x (r n)
    rw [hr 0 n (Nat.zero_le n), Nat.cast_zero, sub_zero, dist_comm (r 0) x] at hh
    dsimp only [a]
    linarith
  obtain ⟨b, ⟨N, rfl⟩, hN⟩ := exists_lt_of_csInf_lt (range_nonempty a)
    (show sInf (range a) < sInf (range a) + 1 by linarith)
  filter_upwards [eventually_ge_atTop N] with n hn
  intro m hnm
  have hn' := hanti hn
  have hm := csInf_le hb (mem_range_self m)
  rw [dist_comm (r m) (r n), hr n m hnm]
  dsimp only [a] at hn' hN hm
  linarith

/-- The chosen cocompact orbit ray has a uniform eventual excess bound for
every starting vertex, with a starting time that may depend on that vertex. -/
theorem cocompactRaySequence_eventual_triangle_excess (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] (ξ : ℝ) (x : Γ) :
    ∀ᶠ n in atTop, ∀ m, n ≤ m →
      dist (x • UpperHalfPlane.I) (cocompactRaySequence Γ ξ n • UpperHalfPlane.I) +
      dist (cocompactRaySequence Γ ξ m • UpperHalfPlane.I)
        (cocompactRaySequence Γ ξ n • UpperHalfPlane.I) -
      dist (x • UpperHalfPlane.I) (cocompactRaySequence Γ ξ m • UpperHalfPlane.I) ≤
        1 + 4 * cocompactOrbitRadius Γ := by
  have ht := geodesic_ray_eventual_triangle_excess
    (fun n : ℕ => finiteBoundaryRay ξ n) (fun m n hmn => by
      rw [finiteBoundaryRay_dist_eq, abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hmn))]
      ring) (x • UpperHalfPlane.I)
  filter_upwards [ht] with n hn
  intro m hnm
  have he := hn m hnm
  have hn' := cocompactRaySequence_bound Γ ξ n
  have hm' := cocompactRaySequence_bound Γ ξ m
  have h₁ := dist_triangle (x • UpperHalfPlane.I) (finiteBoundaryRay ξ n)
    (cocompactRaySequence Γ ξ n • UpperHalfPlane.I)
  have h₂ := dist_triangle4 (cocompactRaySequence Γ ξ m • UpperHalfPlane.I)
    (finiteBoundaryRay ξ m) (finiteBoundaryRay ξ n)
    (cocompactRaySequence Γ ξ n • UpperHalfPlane.I)
  have h₃ := dist_triangle (x • UpperHalfPlane.I)
    (cocompactRaySequence Γ ξ m • UpperHalfPlane.I) (finiteBoundaryRay ξ m)
  rw [dist_comm (finiteBoundaryRay ξ n) (cocompactRaySequence Γ ξ n • UpperHalfPlane.I)] at h₁ h₂
  linarith

end Singularity
