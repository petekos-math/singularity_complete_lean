import Singularity.MetricChains
import Singularity.HyperbolicGrid

/-!
# Short unit-step chains in the upper half-plane

A vertical-horizontal-vertical route gives a chain of at most 3d+5 unit steps.
This coarse bound suffices for the exponential Green lower bound; no geodesic
existence theorem or unformalized metric comparison is assumed.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The point i can be joined to any point by at most 3d+5 unit steps. -/
theorem hyperbolic_unit_chain_from_I (z : ℍ) :
    ∃ (n : ℕ) (p : ℕ → ℍ), p 0 = UpperHalfPlane.I ∧ p n = z ∧
      (n : ℝ) ≤ 3 * dist UpperHalfPlane.I z + 5 ∧
      ∀ k < n, dist (p k) (p (k + 1)) ≤ 1 := by
  let R := dist z UpperHalfPlane.I
  have hR : 0 ≤ R := dist_nonneg
  let v (a t : ℝ) : ℍ := ⟨⟨a, Real.exp t⟩, Real.exp_pos t⟩
  have hv (a : ℝ) : Isometry (v a) := UpperHalfPlane.isometry_vertical_line a
  have hvI : v 0 0 = UpperHalfPlane.I := by apply UpperHalfPlane.ext; apply Complex.ext <;> simp [v]
  have hvz : v z.re (Real.log z.im) = z := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [v, Real.exp_log z.im_pos]
  obtain ⟨hl, hu, hr⟩ := hyperbolic_ball_coordinates (le_refl R)
  have hloglo : -R ≤ Real.log z.im := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (-R)) hl
  have hloghi : Real.log z.im ≤ R := by
    simpa only [Real.log_exp] using Real.log_le_log z.im_pos hu
  have hhorizontal : dist (v 0 R) (v z.re R) ≤ 1 := by
    apply (UpperHalfPlane.dist_le_dist_coe_div_sqrt (v 0 R) (v z.re R)).trans
    have he : dist ((v 0 R : ℍ) : ℂ) ((v z.re R : ℍ) : ℂ) = |z.re| := by
      rw [Complex.dist_of_im_eq (z := ((v 0 R : ℍ) : ℂ)) (w := ((v z.re R : ℍ) : ℂ)) rfl, Real.dist_eq]
      simp [v]
    rw [he]
    change |z.re| / Real.sqrt (Real.exp R * Real.exp R) ≤ 1
    rw [Real.sqrt_mul_self (Real.exp_pos R).le]
    exact (div_le_one (Real.exp_pos R)).mpr hr
  obtain ⟨n, f, hf0, hfn, hn, hf⟩ := isometry_interval_chain (v 0) (hv 0) 0 R
  obtain ⟨m, g, hg0, hgm, hm, hg⟩ :=
    isometry_interval_chain (v z.re) (hv z.re) R (Real.log z.im)
  let b : ℕ → ℍ := fun k => if k = 0 then v 0 R else v z.re R
  have hb : ∀ k < 1, dist (b k) (b (k + 1)) ≤ 1 := by
    intro k hk
    have : k = 0 := by omega
    subst k
    simpa [b] using hhorizontal
  obtain ⟨f', hf'0, hf'n, hf'⟩ := metric_chain_append f b n 1 1 (by simpa [b] using hfn) hf hb
  obtain ⟨p, hp0, hpn, hp⟩ := metric_chain_append f' g (n + 1) m 1
    (by simpa [b, hg0] using hf'n) hf' hg
  refine ⟨n + 1 + m, p, hp0.trans (hf'0.trans (hf0.trans hvI)), hpn.trans (hgm.trans hvz), ?_, hp⟩
  simp only [sub_zero, abs_of_nonneg hR] at hn
  rw [abs_of_nonpos (sub_nonpos.mpr hloghi)] at hm
  rw [dist_comm UpperHalfPlane.I]
  change ((n + 1 + m : ℕ) : ℝ) ≤ 3 * R + 5
  push_cast
  linarith

/-- Isometric transport gives a uniformly short chain between any two points. -/
theorem hyperbolic_unit_chain (z w : ℍ) :
    ∃ (n : ℕ) (p : ℕ → ℍ), p 0 = z ∧ p n = w ∧
      (n : ℝ) ≤ 3 * dist z w + 5 ∧ ∀ k < n, dist (p k) (p (k + 1)) ≤ 1 := by
  let a := z.toSL2R
  obtain ⟨n, p, hp0, hpn, hn, hp⟩ := hyperbolic_unit_chain_from_I (a⁻¹ • w)
  refine ⟨n, fun k => a • p k, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [hp0]; exact UpperHalfPlane.toSL2R_smul_I z
  · dsimp only; rw [hpn]; simp
  · have he : dist UpperHalfPlane.I (a⁻¹ • w) = dist z w := by
      rw [← dist_smul a, smul_inv_smul, UpperHalfPlane.toSL2R_smul_I]
    simpa only [he] using hn
  · intro k hk
    rw [dist_smul]
    exact hp k hk

end Singularity
