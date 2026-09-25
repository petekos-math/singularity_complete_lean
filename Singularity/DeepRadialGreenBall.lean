import Singularity.DeepRadialHarnack
import Singularity.RelativeGreenProductBounds
import Singularity.CocompactGreenBall

/-!
# Product comparison through a ball inside a killed radial domain

If the center's radial depth exceeds the radius plus the fixed interior buffer,
every vertex of the stopping ball lies in the region of the proved Harnack
estimate. The entrance contribution then costs at most exponentially in radius;
the union-killed Green kernel remains the exact additive error.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- A sufficiently deep ball gives an actual killed Green product comparison,
with no assumption about the two external endpoints. -/
theorem cocompact_deep_radial_green_ball_comparison
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ H a b : ℝ, 0 < H ∧ 1 ≤ a ∧ 0 ≤ b ∧
      ∀ (q : SL(2, ℝ)) (r R : ℝ) (u x y : Γ),
      r+H+max R 0 ≤ axisRadialCoordinate (q • (u • UpperHalfPlane.I)) →
      killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y ≤
        killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r ∪
          {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R}) x y +
        a * Real.exp (b*R) * killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x u *
          killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) u y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨H,c,d,hH,hc,hd,hh⟩ := cocompact_deep_radial_greenHarnack Γ s μ hpos hmass hgen hgap
  refine ⟨H,c^2,2*d,hH,by nlinarith,by positivity,?_⟩
  intro q r R u x y hdepth
  let A := radialOrbitSublevel Γ q UpperHalfPlane.I r
  have hfin := finite_hyperbolic_orbit_openBall Γ u R
  let B := hfin.toFinset
  have hB : (B : Set Γ) = {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} := hfin.coe_toFinset
  have hu : r+H ≤ axisRadialCoordinate (q • (u • UpperHalfPlane.I)) := by
    linarith [le_max_right R 0]
  have huA : u ∉ A := by
    intro hh
    change axisRadialCoordinate (q • (u • UpperHalfPlane.I)) ≤ r at hh
    linarith
  have hinside (v : B) : dist ((v : Γ) • UpperHalfPlane.I) (u • UpperHalfPlane.I) ≤ R := by
    have hv : (v : Γ) ∈ (B : Set Γ) := v.property
    rw [hB] at hv
    exact hv.le
  have hvdeep (v : B) : r+H ≤ axisRadialCoordinate (q • ((v : Γ) • UpperHalfPlane.I)) := by
    have hv := axisRadialCoordinate_dist_le (q • ((v : Γ) • UpperHalfPlane.I)) (q • (u • UpperHalfPlane.I))
    rw [dist_smul] at hv
    have hb := (abs_le.mp (hv.trans (hinside v))).1
    linarith [le_max_left R 0]
  let C := c*Real.exp (d*R)
  have hC : 0 ≤ C := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hrow (v z t : Γ)
      (hv : r+H ≤ axisRadialCoordinate (q • (v • UpperHalfPlane.I)))
      (hz : r+H ≤ axisRadialCoordinate (q • (z • UpperHalfPlane.I)))
      (hvz : dist (v • UpperHalfPlane.I) (z • UpperHalfPlane.I) ≤ R) :
      killedGreen s μ A z t ≤ C * killedGreen s μ A v t := by
    apply (hh q r v z t hv hz).trans
    apply mul_le_mul_of_nonneg_right _ (killedGreen_nonneg s μ hμ A v t)
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvz hd.le)) (by linarith)
  have hb := killedGreen_le_union_add_product s μ hμ hmass hgap A B x u y C hC
    (fun v => hrow u v y hu (hvdeep v) (by simpa only [dist_comm] using hinside v))
    (fun v => (killedGreen_diag_ge_one s μ hμ hgap A u huA).trans
      (hrow v u u (hvdeep v) hu (hinside v)))
  have he : C^2 = c^2*Real.exp ((2*d)*R) := by
    dsimp [C]
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  simpa only [hB,he] using hb

end Singularity
