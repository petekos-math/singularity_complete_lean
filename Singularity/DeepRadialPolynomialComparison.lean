import Singularity.DeepRadialGreenBall
import Singularity.CocompactPolynomialComparison

/-!
# Relative product comparison with logarithmic clearance

A logarithmic stopping-ball radius makes the absolute detour error at most
half the actual killed Green lower bound. Its entrance cost is polynomial in
endpoint distance. The center must have room for that ball inside the fixed
deep part of the original domain; this clearance condition is explicit.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- A polynomial killed Green product bound, with the precise logarithmic
clearance needed at the intermediate vertex. It is not uniform relative Ancona. -/
theorem cocompact_deep_radial_polynomial_comparison
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D : ℝ) :
    ∃ H M C p : ℝ, 0 < H ∧ 0 < M ∧ 0 < C ∧ 0 ≤ p ∧
      ∀ (q : SL(2, ℝ)) (r : ℝ) (x u y : Γ),
      r+H ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)) →
      r+H ≤ axisRadialCoordinate (q • (y • UpperHalfPlane.I)) →
      r+H+max (Real.log (M*(1+dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)))) 0 ≤
        axisRadialCoordinate (q • (u • UpperHalfPlane.I)) →
      2 ≤ dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) →
      dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
        dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
        dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y ≤
        C * Real.exp (p*Real.log (1+dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I))) *
          killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x u *
          killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) u y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨H₁,α,β,hH₁,hα,hβ,hlower⟩ := cocompact_deep_radial_killedGreen_exp_lower Γ s μ hpos hmass hgen hgap
  obtain ⟨H₂,c,p,hH₂,hc,hp,hball⟩ := cocompact_deep_radial_green_ball_comparison Γ s μ hpos hmass hgen hgap
  obtain ⟨A,b,hA,hb,hdetour⟩ := killedGreen_hyperbolic_detour_decay_of_excess Γ s μ hμ hgap D
  obtain ⟨M,hM,habsorb⟩ := exists_log_radius_absorption α β A b hα hβ.le hA hb
  let H := max H₁ H₂
  have hH : 0 < H := hH₁.trans_le (le_max_left _ _)
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  refine ⟨H,M,2*c*Real.exp (p*Real.log M),p,hH,hM,by positivity,hp,?_⟩
  intro q r x u y hx hy hu hd hexcess
  let d := dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)
  let R := Real.log (M*(1+d))
  let K := radialOrbitSublevel Γ q UpperHalfPlane.I r
  have hx' : r+H₁ ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)) := by
    linarith [le_max_left H₁ H₂]
  have hy' : r+H₁ ≤ axisRadialCoordinate (q • (y • UpperHalfPlane.I)) := by
    linarith [le_max_left H₁ H₂]
  have hu' : r+H₂+max R 0 ≤ axisRadialCoordinate (q • (u • UpperHalfPlane.I)) := by
    change r+H+max R 0 ≤ _ at hu
    linarith [le_max_right H₁ H₂]
  have hkill : killedGreen s μ (K ∪
      {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R}) x y ≤
      killedGreen s μ K x y/2 := by
    apply (killedGreen_antitone s μ hμ hmass hgap _ _ Set.subset_union_right x y).trans
    apply (hdetour R u x y hd hexcess).trans
    apply (habsorb d dist_nonneg).trans
    have hh := div_le_div_of_nonneg_right (hlower q r x y hx' hy') (show (0 : ℝ) ≤ 2 by norm_num)
    convert hh using 1
    ring
  have hbound := hball q r R u x y hu'
  have hprod : killedGreen s μ K x y ≤
      2*(c*Real.exp (p*R)*killedGreen s μ K x u*killedGreen s μ K u y) := by
    change killedGreen s μ K x y ≤ _ at hbound
    linarith
  have he : Real.exp (p*R) = Real.exp (p*Real.log M)*Real.exp (p*Real.log (1+d)) := by
    dsimp [R]
    rw [Real.log_mul hM.ne' (by positivity), mul_add, Real.exp_add]
  rw [he] at hprod
  convert hprod using 1
  ring

end Singularity
