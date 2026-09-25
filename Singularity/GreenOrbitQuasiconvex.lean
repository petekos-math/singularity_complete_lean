import Singularity.OrbitWordQuasiconvex
import Singularity.GreenWordComparison
import Singularity.QuasiconvexParabolic

/-!
# Green/hyperbolic comparison forces a quasiconvex orbit

Only an upper bound for Green distance by a positive multiple of hyperbolic
distance plus a constant is needed. The spectral Green/word lower bound and
finite-word tracking prove quasiconvexity without an assumed Morse lemma,
relative hyperbolicity, or virtual freeness.
-/

noncomputable section
open Set
open scoped Classical BigOperators MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)

include hne hpos hmass hgen

/-- A radial upper Green/hyperbolic bound implies orbit quasiconvexity. -/
theorem projective_orbit_quasiconvex_of_green_upper (c C : ℝ) (hc : 0 < c)
    (hupper : ∀ g : Γ, greenDistance s μ 1 g ≤ c * dist z (g • z) + C) :
    ∃ D : ℝ, HyperbolicQuasiconvex (MulAction.orbit Γ z) D := by
  obtain ⟨a, b, D, ha, _, _, hcomp⟩ :=
    projectiveNonelementary_greenDistance_word_comparison Γ hne s μ hpos hmass hgen
  apply projective_orbit_quasiconvex_of_radial_word_lower Γ s hgen z (a / c) ((D + C) / c)
    (div_pos ha hc)
  intro g
  rw [show a / c * (wordDistance s hgen 1 g : ℝ) - (D + C) / c =
    (a * (wordDistance s hgen 1 g : ℝ) - (D + C)) / c by ring]
  apply (div_le_iff₀ hc).mpr
  have h := (hcomp 1 g).1.trans (hupper g)
  nlinarith

/-- Bounded additive Green/hyperbolic comparison is more than sufficient.
The scaling factor may be any real number. -/
theorem projective_orbit_quasiconvex_of_green_comparison (δ C : ℝ)
    (hcomp : ∀ g : Γ, |greenDistance s μ 1 g - δ * dist z (g • z)| ≤ C) :
    ∃ D : ℝ, HyperbolicQuasiconvex (MulAction.orbit Γ z) D := by
  apply projective_orbit_quasiconvex_of_green_upper Γ hne s μ hpos hmass hgen z (max δ 1) C
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  intro g
  have h := (abs_le.mp (hcomp g)).2
  have hm := mul_le_mul_of_nonneg_right (le_max_left δ 1) (dist_nonneg (x := z) (y := g • z))
  linarith

/-- In a discrete group with a parabolic, no radial linear upper
Green/hyperbolic bound can hold. No finite-index free subgroup is required. -/
theorem discrete_parabolic_no_green_upper [DiscreteTopology Γ]
    (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ))) :
    ¬∃ c C : ℝ, 0 < c ∧ ∀ h : Γ, greenDistance s μ 1 h ≤ c * dist z (h • z) + C := by
  rintro ⟨c, C, hc, hu⟩
  exact discrete_projective_parabolic_orbit_not_quasiconvex Γ g hpar z
    (projective_orbit_quasiconvex_of_green_upper Γ hne s μ hpos hmass hgen z c C hc hu)

/-- The bounded-comparison obstruction for every discrete nonelementary
projective group containing a parabolic. -/
theorem discrete_parabolic_no_green_comparison [DiscreteTopology Γ]
    (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ))) (δ : ℝ) :
    ¬∃ C : ℝ, ∀ h : Γ, |greenDistance s μ 1 h - δ * dist z (h • z)| ≤ C := by
  rintro ⟨C, hC⟩
  exact discrete_projective_parabolic_orbit_not_quasiconvex Γ g hpar z
    (projective_orbit_quasiconvex_of_green_comparison Γ hne s μ hpos hmass hgen z δ C hC)

end Singularity
