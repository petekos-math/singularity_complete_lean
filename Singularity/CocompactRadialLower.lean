import Singularity.RadialKilledGreen
import Singularity.AxisOrbitChain
import Singularity.KilledGreenChains

/-!
# Coarse killed Green lower bounds along deep axis segments

Cocompactness constructs an orbit chain following the axis while retaining a
uniform radial depth. The verified interior Harnack estimate along this chain
gives an exponential lower bound for actual killed Green values. In particular,
the normalizers do not vanish, even for arbitrarily long segments.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Uniform coarse lower bounds inside radial domains for endpoints in a fixed
axis tube, when its lower end has a fixed positive depth above the boundary. -/
theorem cocompact_radial_killedGreen_exp_lower
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (E : ℝ) :
    ∃ B α β : ℝ, 0 < B ∧ 0 < α ∧ 0 < β ∧
      ∀ (q : SL(2, ℝ)) (r a b : ℝ) (x y : Γ), a ≤ b → r+B ≤ a →
      dist (q • (x • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I a) ≤ E →
      dist (q • (y • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I b) ≤ E →
      α * Real.exp (-β*(b-a)) ≤ killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨D₀,hD₀,hcover⟩ := cocompact_orbit_uniform_bound Γ
  let D := max E D₀
  have hD : 0 < D := hD₀.trans_le (le_max_right E D₀)
  have hED : E ≤ D := le_max_left _ _
  have hcoverD : ∀ z : ℍ, ∃ g : Γ, dist (g • UpperHalfPlane.I) z ≤ D := by
    intro z
    obtain ⟨g,hg⟩ := hcover z
    exact ⟨g,hg.trans (le_max_right E D₀)⟩
  obtain ⟨R,C,hR,hC,hlocal⟩ := radial_killedGreen_uniform_harnack Γ s μ hpos hgen hgap hmass (2*D+1)
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨R+D,Real.exp (-4*Real.log C),Real.log C+1,by positivity,Real.exp_pos _,by positivity,?_⟩
  intro q r a b x y hab hdepth hx hy
  obtain ⟨N,f,hf0,hfN,hN,hstep,hcoord⟩ := axis_orbit_chain_of_cover Γ D hD.le hcoverD
    q a b hab x y (hx.trans hED) (hy.trans hED)
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
  nlinarith

/-- For any fixed tube radius there is one depth buffer ensuring that every
such killed Green normalizer is strictly positive, independently of length. -/
theorem cocompact_radial_killedGreen_pos
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (E : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : SL(2, ℝ)) (r a b : ℝ) (x y : Γ), a ≤ b → r+B ≤ a →
      dist (q • (x • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I a) ≤ E →
      dist (q • (y • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I b) ≤ E →
      0 < killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y := by
  obtain ⟨B,α,β,hB,hα,_hβ,hlower⟩ := cocompact_radial_killedGreen_exp_lower Γ s μ hpos hmass hgen hgap E
  refine ⟨B,hB,?_⟩
  intro q r a b x y hab hdepth hx hy
  exact (mul_pos hα (Real.exp_pos _)).trans_le (hlower q r a b x y hab hdepth hx hy)

end Singularity
