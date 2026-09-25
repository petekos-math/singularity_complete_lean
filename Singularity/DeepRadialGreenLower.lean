import Singularity.RadialKilledGreen
import Singularity.DeepRadialOrbitChain
import Singularity.KilledGreenChains

/-!
# Uniform killed Green lower bounds throughout deep radial domains

Geodesic convexity removes the fixed-axis-tube restriction. Any two endpoints
above a fixed radial depth are connected by a short interior orbit chain,
giving a coarse exponential lower bound in their actual hyperbolic distance.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Coarse exponential lower bounds for all pairs of sufficiently deep endpoints,
uniformly in the isometric chart and killing level. -/
theorem cocompact_deep_radial_killedGreen_exp_lower
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ H α β : ℝ, 0 < H ∧ 0 < α ∧ 0 < β ∧ ∀ (q : SL(2, ℝ)) (r : ℝ) (x y : Γ),
      r+H ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)) →
      r+H ≤ axisRadialCoordinate (q • (y • UpperHalfPlane.I)) →
      α * Real.exp (-β*dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) ≤
        killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨E,hE,hcover⟩ := cocompact_orbit_uniform_bound Γ
  obtain ⟨R,C,hR,hC,hlocal⟩ := radial_killedGreen_uniform_harnack Γ s μ hpos hgen hgap hmass (2*E+1)
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨R+E,Real.exp (-4*Real.log C),Real.log C+1,by positivity,Real.exp_pos _,by positivity,?_⟩
  intro q r x y hx hy
  obtain ⟨N,f,hf0,hfN,hN,hstep,hcoord⟩ := deep_radial_orbit_chain_of_cover Γ E hE.le hcover
    q (r+(R+E)) x y hx hy
  have hdeep (k : ℕ) (hk : k ≤ N) :
      r+R ≤ axisRadialCoordinate (q • (f k • UpperHalfPlane.I)) := by
    have hh := hcoord k hk
    linarith
  have hend : f N ∉ radialOrbitSublevel Γ q UpperHalfPlane.I r := by
    intro hn
    have hh := hdeep N le_rfl
    change axisRadialCoordinate (q • (f N • UpperHalfPlane.I)) ≤ r at hn
    linarith
  have hg := killedGreen_lower_of_harnack_chain s μ hμ hgap
    (radialOrbitSublevel Γ q UpperHalfPlane.I r) C hCp f N hend
    (fun k hk y => hlocal q r (f k) (f (k+1)) (hstep k hk)
      (hdeep k (by omega)) (hdeep (k+1) (by omega)) y)
  rw [hf0,hfN] at hg
  apply le_trans _ hg
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hN hlog
  nlinarith [dist_nonneg (x := x • UpperHalfPlane.I) (y := y • UpperHalfPlane.I)]

/-- Every pair beyond a single radial depth buffer has a positive killed Green
entry. In particular the corresponding normalization denominators are nonzero. -/
theorem cocompact_deep_radial_killedGreen_pos
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ H : ℝ, 0 < H ∧ ∀ (q : SL(2, ℝ)) (r : ℝ) (x y : Γ),
      r+H ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)) →
      r+H ≤ axisRadialCoordinate (q • (y • UpperHalfPlane.I)) →
      0 < killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y := by
  obtain ⟨H,α,β,hH,hα,_hβ,hlower⟩ := cocompact_deep_radial_killedGreen_exp_lower Γ s μ hpos hmass hgen hgap
  refine ⟨H,hH,?_⟩
  intro q r x y hx hy
  exact (mul_pos hα (Real.exp_pos _)).trans_le (hlower q r x y hx hy)

end Singularity
