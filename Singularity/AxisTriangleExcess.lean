import Singularity.HyperbolicAxisNormalization

/-!
# Bounded triangle excess gives a nearby segment point

For an axis segment of length t and a point z, the balanced parameter
u = (d(z,i) - d(z,axis(t)) + t)/2 lies in [0,t]. Explicit hyperbolic
cosine estimates give d(z,axis(u)) ≤ excess/2 + log 4. Thus a bounded-excess
condition implies the segment-neighborhood condition in the Ancona theorem.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Exponential-coordinate formula for distance to the normalized axis. -/
theorem cosh_dist_axis (z : ℍ) (t : ℝ) :
    Real.cosh (dist z (verticalHeightRay UpperHalfPlane.I t)) =
      ((z.re ^ 2 + z.im ^ 2) * Real.exp (-t) + Real.exp t) / (2 * z.im) := by
  rw [UpperHalfPlane.cosh_dist']
  change ((z.re - 0) ^ 2 + z.im ^ 2 + (Real.exp t * 1) ^ 2) /
    (2 * z.im * (Real.exp t * 1)) = _
  rw [Real.exp_neg]
  field_simp
  ring

/-- Two endpoint cosines control the cosine at any axis parameter. -/
theorem cosh_dist_axis_interpolation (z : ℍ) (t u : ℝ) :
    Real.cosh (dist z (verticalHeightRay UpperHalfPlane.I u)) ≤
      Real.exp (-u) * Real.cosh (dist z UpperHalfPlane.I) +
      Real.exp (u-t) * Real.cosh (dist z (verticalHeightRay UpperHalfPlane.I t)) := by
  have hzero := cosh_dist_axis z 0
  simp only [verticalHeightRay_zero, neg_zero, Real.exp_zero, mul_one] at hzero
  rw [cosh_dist_axis, cosh_dist_axis, hzero]
  have hA : 0 ≤ z.re ^ 2 + z.im ^ 2 := by positivity
  have he : Real.exp (u-t) * Real.exp t = Real.exp u := by rw [← Real.exp_add]; congr 1; ring
  have hn : (z.re ^ 2 + z.im ^ 2) * Real.exp (-u) + Real.exp u ≤
      Real.exp (-u) * (z.re ^ 2 + z.im ^ 2 + 1) +
      Real.exp (u-t) * ((z.re ^ 2 + z.im ^ 2) * Real.exp (-t) + Real.exp t) := by
    nlinarith [Real.exp_pos (-u),
      mul_nonneg (Real.exp_pos (u-t)).le (mul_nonneg hA (Real.exp_pos (-t)).le)]
  calc
    _ ≤ (Real.exp (-u) * (z.re ^ 2 + z.im ^ 2 + 1) +
      Real.exp (u-t) * ((z.re ^ 2 + z.im ^ 2) * Real.exp (-t) + Real.exp t)) / (2 * z.im) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by ring

/-- The balanced parameter is on the segment and is close to the middle point. -/
theorem axis_balanced_point (z : ℍ) (t : ℝ) (ht : 0 ≤ t) :
    let u := (dist z UpperHalfPlane.I - dist z (verticalHeightRay UpperHalfPlane.I t) + t) / 2
    u ∈ Set.Icc 0 t ∧
      dist z (verticalHeightRay UpperHalfPlane.I u) ≤
        (dist z UpperHalfPlane.I + dist z (verticalHeightRay UpperHalfPlane.I t) - t) / 2 + Real.log 4 := by
  let a := dist z UpperHalfPlane.I
  let b := dist z (verticalHeightRay UpperHalfPlane.I t)
  let u := (a-b+t)/2
  let e := (a+b-t)/2
  change u ∈ Set.Icc 0 t ∧ dist z (verticalHeightRay UpperHalfPlane.I u) ≤ e + Real.log 4
  have hd : dist UpperHalfPlane.I (verticalHeightRay UpperHalfPlane.I t) = t :=
    verticalHeightRay_dist UpperHalfPlane.I ht
  have htri₁ := dist_triangle z UpperHalfPlane.I (verticalHeightRay UpperHalfPlane.I t)
  have htri₂ := dist_triangle z (verticalHeightRay UpperHalfPlane.I t) UpperHalfPlane.I
  rw [hd] at htri₁
  rw [dist_comm (verticalHeightRay UpperHalfPlane.I t) UpperHalfPlane.I, hd] at htri₂
  have hau : -u + a = e := by dsimp [u, e]; ring
  have hbu : u-t+b = e := by dsimp [u, e]; ring
  refine ⟨⟨by dsimp [u,a,b]; linarith, by dsimp [u,a,b]; linarith⟩, ?_⟩
  have hcosh : Real.cosh (dist z (verticalHeightRay UpperHalfPlane.I u)) ≤ 2 * Real.exp e := by
    calc
      _ ≤ Real.exp (-u) * Real.cosh a + Real.exp (u-t) * Real.cosh b :=
        cosh_dist_axis_interpolation z t u
      _ ≤ Real.exp (-u) * Real.exp a + Real.exp (u-t) * Real.exp b :=
        add_le_add (mul_le_mul_of_nonneg_left (cosh_le_exp_of_nonneg _ dist_nonneg) (Real.exp_pos _).le)
          (mul_le_mul_of_nonneg_left (cosh_le_exp_of_nonneg _ dist_nonneg) (Real.exp_pos _).le)
      _ = 2 * Real.exp e := by rw [← Real.exp_add, ← Real.exp_add, hau, hbu]; ring
  have hexp : Real.exp (dist z (verticalHeightRay UpperHalfPlane.I u)) ≤
      2 * Real.cosh (dist z (verticalHeightRay UpperHalfPlane.I u)) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-dist z (verticalHeightRay UpperHalfPlane.I u))]
  apply Real.exp_le_exp.mp
  calc
    _ ≤ 4 * Real.exp e := by linarith
    _ = Real.exp (e + Real.log 4) := by rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<4)]; ring

/-- Every bounded-excess triple has a point on its constructed endpoint
segment at distance at most D/2 + log 4 from the middle point. -/
theorem exists_axis_point_of_triangle_excess (x o y : ℍ) (D : ℝ)
    (hexcess : dist x o + dist y o - dist x y ≤ D) :
    ∃ (g : SL(2, ℝ)) (u : ℝ),
      g • UpperHalfPlane.I = x ∧ g • verticalHeightRay UpperHalfPlane.I (dist x y) = y ∧
      u ∈ Set.Icc 0 (dist x y) ∧
      dist (g • verticalHeightRay UpperHalfPlane.I u) o ≤ D / 2 + Real.log 4 := by
  obtain ⟨g, hx, hy⟩ := exists_oriented_hyperbolic_axis x y
  let z := g⁻¹ • o
  obtain ⟨hu, hclose⟩ := axis_balanced_point z (dist x y) dist_nonneg
  let u := (dist z UpperHalfPlane.I - dist z (verticalHeightRay UpperHalfPlane.I (dist x y)) + dist x y)/2
  have h₁ : dist z UpperHalfPlane.I = dist x o := by
    rw [← dist_smul g, smul_inv_smul, hx, dist_comm]
  have h₂ : dist z (verticalHeightRay UpperHalfPlane.I (dist x y)) = dist y o := by
    rw [← dist_smul g, smul_inv_smul, hy, dist_comm]
  refine ⟨g, u, hx, hy, hu, ?_⟩
  have he : dist (g • verticalHeightRay UpperHalfPlane.I u) o =
      dist z (verticalHeightRay UpperHalfPlane.I u) := by
    calc
      _ = dist (g • z) (g • verticalHeightRay UpperHalfPlane.I u) := by
        dsimp [z]; rw [smul_inv_smul, dist_comm]
      _ = _ := dist_smul g _ _
  rw [he]
  change dist z (verticalHeightRay UpperHalfPlane.I u) ≤
    (dist z UpperHalfPlane.I + dist z (verticalHeightRay UpperHalfPlane.I (dist x y)) - dist x y) / 2 + Real.log 4 at hclose
  rw [h₁, h₂] at hclose
  linarith

end Singularity
