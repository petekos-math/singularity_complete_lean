import Singularity.CocompactGlobalHarnack
import Singularity.GreenProductBounds

/-!
# Green comparison through a hyperbolic ball

The entrance part is controlled by a product through the center with a cost
at most exponential in the ball radius. The killed Green kernel is the exact
additive error, so no avoidance probability or boundary limit is assumed.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A bounded open ball contains only finitely many group vertices, with all
stabilizer multiplicities retained. -/
theorem finite_hyperbolic_orbit_openBall (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (u : Γ) (R : ℝ) :
    {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R}.Finite := by
  apply (finite_group_vertices_in_compact Γ UpperHalfPlane.I
    (isCompact_closedBall (u • UpperHalfPlane.I) R)).subset
  intro g hg
  change dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R at hg
  exact hg.le

/-- A ball of radius R gives a product comparison with exponential cost and
the actual killed Green kernel as remainder. -/
theorem cocompact_walkGreen_ball_comparison (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 ≤ b ∧ ∀ (R : ℝ) (u x y : Γ),
      walkGreen s μ x y ≤
        killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} x y +
        a * Real.exp (b * R) * walkGreen s μ x u * walkGreen s μ u y := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨c, d, hc, hd, hh⟩ := cocompact_global_greenHarnack Γ s μ hpos hgen hgap
  refine ⟨c ^ 2, 2 * d, by nlinarith, by positivity, ?_⟩
  intro R u x y
  have hfin := finite_hyperbolic_orbit_openBall Γ u R
  let A := hfin.toFinset
  have hA : (A : Set Γ) = {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} :=
    hfin.coe_toFinset
  let C := c * Real.exp (d * R)
  have hC : 0 ≤ C := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hrow (v z t : Γ) (hvz : dist (v • UpperHalfPlane.I) (z • UpperHalfPlane.I) ≤ R) :
      walkGreen s μ z t ≤ C * walkGreen s μ v t := by
    apply (hh v z t).trans
    apply mul_le_mul_of_nonneg_right _ (walkGreen_nonneg s μ hμ v t)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvz hd)) (by linarith)
  have hinside (a : A) : dist ((a : Γ) • UpperHalfPlane.I) (u • UpperHalfPlane.I) ≤ R := by
    have ha : (a : Γ) ∈ (A : Set Γ) := a.property
    rw [hA] at ha
    exact ha.le
  have hbound := walkGreen_le_killed_add_product s μ hμ hmass hgap A x u y C hC
    (fun a => hrow u a y (by simpa only [dist_comm] using hinside a))
    (fun a => (walkGreen_diag_ge_one s μ hμ hgap u).trans (hrow a u u (hinside a)))
  have he : C ^ 2 = c ^ 2 * Real.exp ((2 * d) * R) := by
    dsimp [C]
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  simpa only [hA, he] using hbound

end Singularity
