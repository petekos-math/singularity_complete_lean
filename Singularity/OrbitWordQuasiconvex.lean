import Singularity.QuasigeodesicTracking
import Singularity.WordGeodesics

/-!
# Linear word-distance lower bounds force orbit quasiconvexity

For an isometric action on the hyperbolic plane, finitely many generators give
a uniform jump bound. The images of shortest word paths are therefore finite
quasigeodesics whenever orbit distances have a linear word-distance lower bound.
The tracking theorem then proves quasiconvexity of the actual orbit.
-/

noncomputable section
open Set
open scoped Classical BigOperators MatrixGroups UpperHalfPlane

namespace Singularity

/-- An orbit with a linear lower word-distance bound is quasiconvex. The
isometry hypothesis is explicit, so the theorem applies to either SL or PSL. -/
theorem hyperbolicQuasiconvex_orbit_of_word_lower
    (Γ : Type*) [Group Γ] [MulAction Γ ℍ]
    (hisom : ∀ (g : Γ) (u v : ℍ), dist (g • u) (g • v) = dist u v)
    (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (z : ℍ) (a b : ℝ) (ha : 0 < a)
    (hlower : ∀ x y : Γ, a * (wordDistance s hgen x y : ℝ) - b ≤ dist (x • z) (y • z)) :
    HyperbolicQuasiconvex (MulAction.orbit Γ z)
      (quasigeodesicTrackingRadius a b (∑ g ∈ symmetricWordSupport s, dist z (g • z))) := by
  apply hyperbolicQuasiconvex_of_chains _ a b _ ha
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨p, hp0, hpN, hstep, hgeo⟩ := wordDistance_geodesic_chain s hgen x y
  refine ⟨wordDistance s hgen x y, fun k => p k • z, ?_, ?_, ?_, ?_, ?_⟩
  · change p 0 • z = x • z
    rw [hp0]
  · change p (wordDistance s hgen x y) • z = y • z
    rw [hpN]
  · intro k _; exact ⟨p k, rfl⟩
  · intro k hk
    obtain ⟨g, hg, he⟩ := hstep k hk
    change dist (p k • z) (p (k + 1) • z) ≤ _
    rw [he, mul_smul, hisom]
    exact Finset.single_le_sum (f := fun g : Γ => dist z (g • z)) (fun _ _ => dist_nonneg) hg
  · intro i hi j hj
    simpa only [hgeo i hi j hj] using hlower (p i) (p j)

/-- The concrete projective orbit version, with no assumed discreteness. -/
theorem projective_orbit_quasiconvex_of_word_lower (Γ : Subgroup PSL(2, ℝ))
    (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (z : ℍ) (a b : ℝ) (ha : 0 < a)
    (hlower : ∀ x y : Γ, a * (wordDistance s hgen x y : ℝ) - b ≤ dist (x • z) (y • z)) :
    ∃ D : ℝ, HyperbolicQuasiconvex (MulAction.orbit Γ z) D := by
  refine ⟨_, hyperbolicQuasiconvex_orbit_of_word_lower Γ ?_ s hgen z a b ha hlower⟩
  intro g u v
  exact projective_dist_smul (g : PSL(2, ℝ)) u v

/-- By left invariance it suffices to assume the word-distance bound from the
identity; it then holds between every pair of orbit vertices. -/
theorem projective_orbit_quasiconvex_of_radial_word_lower (Γ : Subgroup PSL(2, ℝ))
    (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (z : ℍ) (a b : ℝ) (ha : 0 < a)
    (hlower : ∀ g : Γ, a * (wordDistance s hgen 1 g : ℝ) - b ≤ dist z (g • z)) :
    ∃ D : ℝ, HyperbolicQuasiconvex (MulAction.orbit Γ z) D := by
  apply projective_orbit_quasiconvex_of_word_lower Γ s hgen z a b ha
  intro x y
  have hw : wordDistance s hgen 1 (x⁻¹ * y) = wordDistance s hgen x y := by
    simpa only [inv_mul_cancel] using wordDistance_left s hgen x⁻¹ x y
  have hd : dist z ((x⁻¹ * y) • z) = dist (x • z) (y • z) := by
    have h := projective_dist_smul (x : PSL(2, ℝ)) z ((x⁻¹ * y) • z)
    change dist (x • z) (x • ((x⁻¹ * y) • z)) = _ at h
    simpa only [← mul_smul, mul_inv_cancel_left] using h.symm
  simpa only [hw, hd] using hlower (x⁻¹ * y)

end Singularity
