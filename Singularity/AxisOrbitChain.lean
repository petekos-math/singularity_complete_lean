import Singularity.RadialCoordinate
import Singularity.AxisBallSeparation
import Singularity.CocompactRayApproximation
import Singularity.MetricChains

/-!
# Short orbit chains retaining a radial depth bound

Subdivide an oriented axis interval, approximate its points by a dense orbit,
and keep the prescribed vertices at the ends. All chain vertices remain above
the lower endpoint's radial coordinate minus the approximation radius.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Subdivision of an ordered real interval, with every sample inside it. -/
theorem ordered_interval_subdivision (a b : ℝ) (hab : a ≤ b) :
    ∃ (n : ℕ) (τ : ℕ → ℝ), τ 0 = a ∧ τ n = b ∧ (n : ℝ) ≤ b-a+2 ∧
      (∀ k ≤ n, a ≤ τ k ∧ τ k ≤ b) ∧ ∀ k < n, |τ (k+1)-τ k| ≤ 1 := by
  let n := ⌈b-a⌉₊+1
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hlen : b-a ≤ (n : ℝ) := by
    have hh := Nat.le_ceil (b-a)
    dsimp [n]; push_cast; linarith
  let τ := fun k : ℕ => a+(b-a)*(k:ℝ)/n
  refine ⟨n,τ,by simp [τ],?_,?_,?_,?_⟩
  · dsimp [τ]; field_simp; ring
  · have hh := Nat.ceil_lt_add_one (sub_nonneg.mpr hab)
    dsimp [n]; push_cast; linarith
  · intro k hk
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast hk
    have hlo : 0 ≤ (b-a)*(k:ℝ)/n := by positivity
    have hhi : (b-a)*(k:ℝ)/n ≤ b-a := by
      apply (div_le_iff₀ hn).mpr
      exact mul_le_mul_of_nonneg_left hk' (sub_nonneg.mpr hab)
    dsimp [τ]
    constructor <;> linarith
  · intro k _
    have he : τ (k+1)-τ k = (b-a)/n := by dsimp [τ]; push_cast; ring
    rw [he, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hab) hn.le)]
    exact (div_le_one hn).mpr hlen

/-- An axis tube contains a short chain of orbit vertices with prescribed ends;
every vertex stays within the same radius of a point of the finite axis segment. -/
theorem axis_orbit_chain_with_tube (Γ : Subgroup SL(2, ℝ)) (E : ℝ) (_hE : 0 ≤ E)
    (hcover : ∀ z : ℍ, ∃ g : Γ, dist (g • UpperHalfPlane.I) z ≤ E)
    (q : SL(2, ℝ)) (a b : ℝ) (hab : a ≤ b) (x y : Γ)
    (hx : dist (q • (x • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I a) ≤ E)
    (hy : dist (q • (y • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I b) ≤ E) :
    ∃ (N : ℕ) (f : ℕ → Γ), f 0 = x ∧ f N = y ∧ (N : ℝ) ≤ b-a+4 ∧
      (∀ k < N, dist (f k • UpperHalfPlane.I) (f (k+1) • UpperHalfPlane.I) ≤ 2*E+1) ∧
      ∀ k ≤ N, ∃ t ∈ Set.Icc a b,
        dist (q • (f k • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I t) ≤ E := by
  obtain ⟨n,τ,hτ0,hτn,hn,hτrange,hτstep⟩ := ordered_interval_subdivision a b hab
  choose p hp using fun k : ℕ => hcover (q⁻¹ • verticalHeightRay UpperHalfPlane.I (τ k))
  have hp' (k : ℕ) : dist (q • (p k • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I (τ k)) ≤ E := by
    have hh := hp k
    rw [← dist_smul q] at hh
    simpa only [smul_inv_smul] using hh
  have hpstep (k : ℕ) (hk : k < n) :
      dist (p k • UpperHalfPlane.I) (p (k+1) • UpperHalfPlane.I) ≤ 2*E+1 := by
    rw [← dist_smul q]
    have hh := dist_triangle4 (q • (p k • UpperHalfPlane.I))
      (verticalHeightRay UpperHalfPlane.I (τ k)) (verticalHeightRay UpperHalfPlane.I (τ (k+1)))
      (q • (p (k+1) • UpperHalfPlane.I))
    rw [verticalHeightRay_dist_eq, abs_sub_comm (τ k)] at hh
    have hend := hp' (k+1)
    rw [dist_comm] at hend
    linarith [hp' k, hτstep k hk]
  have hfirst : dist (x • UpperHalfPlane.I) (p 0 • UpperHalfPlane.I) ≤ 2*E+1 := by
    rw [← dist_smul q]
    have hh := dist_triangle (q • (x • UpperHalfPlane.I))
      (verticalHeightRay UpperHalfPlane.I a) (q • (p 0 • UpperHalfPlane.I))
    have hp0 := hp' 0
    rw [hτ0, dist_comm] at hp0
    linarith
  have hlast : dist (p n • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ 2*E+1 := by
    rw [← dist_smul q]
    have hh := dist_triangle (q • (p n • UpperHalfPlane.I))
      (verticalHeightRay UpperHalfPlane.I b) (q • (y • UpperHalfPlane.I))
    have hpn := hp' n
    rw [hτn] at hpn
    rw [dist_comm] at hy
    linarith
  let f : ℕ → Γ := fun k => if k=0 then x else if k≤n+1 then p (k-1) else y
  refine ⟨n+2,f,by simp [f],by simp [f],?_,?_,?_⟩
  · push_cast; linarith
  · intro k hk
    by_cases hk0 : k=0
    · subst k
      simpa [f] using hfirst
    · by_cases hkn : k≤n
      · have hh := hpstep (k-1) (by omega)
        simpa only [f, ite_eq_right hk0, ite_eq_right (show k+1≠0 by omega),
          ite_eq_left (show k≤n+1 by omega), ite_eq_left (show k+1≤n+1 by omega),
          show k+1-1=k by omega, show k-1+1=k by omega] using hh
      · have he : k=n+1 := by omega
        subst k
        simpa [f] using hlast
  · intro k hk
    by_cases hk0 : k=0
    · subst k
      exact ⟨a,⟨le_rfl,hab⟩,by simpa [f] using hx⟩
    · by_cases hkn : k≤n+1
      · refine ⟨τ (k-1),hτrange (k-1) (by omega),?_⟩
        simpa only [f, ite_eq_right hk0, ite_eq_left hkn] using hp' (k-1)
      · exact ⟨b,⟨hab,le_rfl⟩,by simpa only [f, ite_eq_right hk0, ite_eq_right hkn] using hy⟩

/-- The tube construction gives the radial depth estimate used by the original
axis lower-bound argument. -/
theorem axis_orbit_chain_of_cover (Γ : Subgroup SL(2, ℝ)) (E : ℝ) (hE : 0 ≤ E)
    (hcover : ∀ z : ℍ, ∃ g : Γ, dist (g • UpperHalfPlane.I) z ≤ E)
    (q : SL(2, ℝ)) (a b : ℝ) (hab : a ≤ b) (x y : Γ)
    (hx : dist (q • (x • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I a) ≤ E)
    (hy : dist (q • (y • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I b) ≤ E) :
    ∃ (N : ℕ) (f : ℕ → Γ), f 0 = x ∧ f N = y ∧ (N : ℝ) ≤ b-a+4 ∧
      (∀ k < N, dist (f k • UpperHalfPlane.I) (f (k+1) • UpperHalfPlane.I) ≤ 2*E+1) ∧
      ∀ k ≤ N, a-E ≤ axisRadialCoordinate (q • (f k • UpperHalfPlane.I)) := by
  obtain ⟨N,f,hf0,hfN,hN,hstep,htube⟩ := axis_orbit_chain_with_tube Γ E hE hcover q a b hab x y hx hy
  refine ⟨N,f,hf0,hfN,hN,hstep,?_⟩
  intro k hk
  obtain ⟨t,ht,hclose⟩ := htube k hk
  have hh := (axisRadialCoordinate_near_axis _ t E hclose).1
  linarith [ht.1]

end Singularity
