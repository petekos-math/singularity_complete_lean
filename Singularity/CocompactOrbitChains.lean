import Singularity.HyperbolicChains
import Singularity.CocompactRayApproximation

/-!
# Short chains in a cocompact hyperbolic orbit

The explicitly constructed unit-step chains in the plane are approximated by
orbit points. The original group vertices, including their stabilizer data,
are retained as the endpoints.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A D-dense orbit has chains of at most 3d+7 steps, each of length at most
2D+1, with prescribed group vertices at both ends. -/
theorem hyperbolic_orbit_chain_of_cover (Γ : Subgroup SL(2, ℝ)) (D : ℝ) (hD : 0 ≤ D)
    (hcover : ∀ z : ℍ, ∃ g : Γ, dist (g • UpperHalfPlane.I) z ≤ D) (x y : Γ) :
    ∃ (N : ℕ) (f : ℕ → Γ), f 0 = x ∧ f N = y ∧
      (N : ℝ) ≤ 3 * dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) + 7 ∧
      ∀ k < N, dist (f k • UpperHalfPlane.I) (f (k + 1) • UpperHalfPlane.I) ≤ 2 * D + 1 := by
  obtain ⟨n, p, hp0, hpn, hn, hp⟩ := hyperbolic_unit_chain (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)
  choose q hq using fun k : ℕ => hcover (p k)
  have hqstep (k : ℕ) (hk : k < n) :
      dist (q k • UpperHalfPlane.I) (q (k + 1) • UpperHalfPlane.I) ≤ 2 * D + 1 := by
    have hd := dist_triangle4 (q k • UpperHalfPlane.I) (p k) (p (k + 1)) (q (k + 1) • UpperHalfPlane.I)
    have hlast := hq (k + 1)
    rw [dist_comm (q (k + 1) • UpperHalfPlane.I)] at hlast
    linarith [hq k, hp k hk]
  let f : ℕ → Γ := fun k => if k = 0 then x else if k ≤ n + 1 then q (k - 1) else y
  refine ⟨n + 2, f, by simp [f], by simp [f], ?_, ?_⟩
  · push_cast
    linarith
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      have hh : dist (x • UpperHalfPlane.I) (q 0 • UpperHalfPlane.I) ≤ D := by
        simpa only [hp0, dist_comm] using hq 0
      simp only [f, ite_eq_left rfl, show (0 + 1 : ℕ) ≠ 0 by omega,
        show (0 + 1 : ℕ) ≤ n + 1 by omega, Nat.add_sub_cancel, ite_eq_left]
      exact hh.trans (by linarith)
    · by_cases hkn : k ≤ n
      · have hj := hqstep (k - 1) (by omega)
        have hk1 : k + 1 ≠ 0 := by omega
        simpa only [f, ite_eq_right hk0, ite_eq_right hk1,
          ite_eq_left (show k ≤ n + 1 by omega), ite_eq_left (show k + 1 ≤ n + 1 by omega),
          show k + 1 - 1 = k by omega, show k - 1 + 1 = k by omega] using hj
      · have hke : k = n + 1 := by omega
        subst k
        have hh : dist (q n • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D := by
          simpa only [hpn] using hq n
        simpa [f] using hh.trans (show D ≤ 2 * D + 1 by linarith)

/-- Cocompactness supplies one jump bound for short chains between all group vertices. -/
theorem cocompact_hyperbolic_orbit_chains (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    ∃ L : ℝ, 0 < L ∧ ∀ x y : Γ,
      ∃ (N : ℕ) (f : ℕ → Γ), f 0 = x ∧ f N = y ∧
        (N : ℝ) ≤ 3 * dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) + 7 ∧
        ∀ k < N, dist (f k • UpperHalfPlane.I) (f (k + 1) • UpperHalfPlane.I) ≤ L := by
  obtain ⟨D, hD, hcover⟩ := cocompact_orbit_uniform_bound Γ
  exact ⟨2 * D + 1, by positivity, hyperbolic_orbit_chain_of_cover Γ D hD.le hcover⟩

end Singularity
