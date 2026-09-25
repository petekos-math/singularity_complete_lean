import Singularity.CayleyMetric
import Singularity.GeometricStrip
import Singularity.KilledWalk

/-!
# Length of paths avoiding a hyperbolic ball

Outside the radius-R ball about i, a bounded hyperbolic jump moves by at most
4 exp(L-R) in the disk coordinate. A finite path with separated disk endpoints
therefore has exponentially many steps. This is a geometric statement about
actual permitted words; no Martin-boundary identification is used.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- On the nonnegative axis the hyperbolic cosine is at most the exponential. -/
theorem cosh_le_exp_of_nonneg (t : ℝ) (ht : 0 ≤ t) : Real.cosh t ≤ Real.exp t := by
  rw [Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -t ≤ t by linarith)
  linarith

/-- Away from zero the hyperbolic sine is bounded below exponentially. -/
theorem exp_le_four_sinh (t : ℝ) (ht : 1 ≤ t) : Real.exp t ≤ 4 * Real.sinh t := by
  have he : 2 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hn : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq]
  linarith

/-- Bounded triangle excess at i gives a quantitative separation in the disk,
provided the endpoints are at least hyperbolic distance two apart. -/
theorem halfPlaneCayley_dist_lower_of_excess (z w : ℍ) (D : ℝ)
    (hd : 2 ≤ dist z w)
    (hexcess : dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - dist z w ≤ D) :
    Real.exp (-D / 2) / 4 ≤ dist (halfPlaneCayley z) (halfPlaneCayley w) := by
  have hden : Real.cosh (dist z UpperHalfPlane.I / 2) * Real.cosh (dist w UpperHalfPlane.I / 2) ≤
      Real.exp ((dist z UpperHalfPlane.I + dist w UpperHalfPlane.I) / 2) := by
    calc
      _ ≤ Real.exp (dist z UpperHalfPlane.I / 2) * Real.exp (dist w UpperHalfPlane.I / 2) :=
        mul_le_mul (cosh_le_exp_of_nonneg _ (by positivity))
          (cosh_le_exp_of_nonneg _ (by positivity)) (Real.cosh_pos _).le (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hs := exp_le_four_sinh (dist z w / 2) (by linarith)
  rw [halfPlaneCayley_dist]
  apply (le_div_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))).mpr
  calc
    _ ≤ (Real.exp (-D / 2) / 4) *
        Real.exp ((dist z UpperHalfPlane.I + dist w UpperHalfPlane.I) / 2) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = Real.exp ((dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - D) / 2) / 4 := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp (dist z w / 2) / 4 :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ ≤ _ := by linarith

/-- The triangle-excess separation estimate in the disk chart centered at an
arbitrary orbit point. -/
theorem orbit_cayley_separation_of_excess (Γ : Subgroup SL(2, ℝ))
    (u x y : Γ) (D : ℝ) (hd : 2 ≤ dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I))
    (hexcess : dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
      dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
      dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D) :
    Real.exp (-D / 2) / 4 ≤ dist
      (halfPlaneCayley ((u⁻¹ * x) • UpperHalfPlane.I))
      (halfPlaneCayley ((u⁻¹ * y) • UpperHalfPlane.I)) := by
  have he (g h : Γ) : dist ((u⁻¹ * g) • UpperHalfPlane.I) ((u⁻¹ * h) • UpperHalfPlane.I) =
      dist (g • UpperHalfPlane.I) (h • UpperHalfPlane.I) := by
    simp only [mul_smul]
    change dist (((u⁻¹ : Γ) : SL(2, ℝ)) • (g • UpperHalfPlane.I))
      (((u⁻¹ : Γ) : SL(2, ℝ)) • (h • UpperHalfPlane.I)) = _
    rw [dist_smul]
  have hc (g : Γ) : dist ((u⁻¹ * g) • UpperHalfPlane.I) UpperHalfPlane.I =
      dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) := by
    simpa only [inv_mul_cancel, one_smul] using he g u
  apply halfPlaneCayley_dist_lower_of_excess _ _ D
  · simpa only [he] using hd
  · simpa only [hc, he] using hexcess

/-- A path avoiding the open ball has exponentially small total disk movement
per step. Only positions strictly before its endpoint need to avoid the ball. -/
theorem walkEndpoint_cayley_detour_bound (Γ : Subgroup SL(2, ℝ))
    (s : Finset Γ) (R : ℝ) (n : ℕ) (x : Γ) (w : WalkWord s n)
    (hw : avoidsBefore s {g : Γ | dist (g • UpperHalfPlane.I) UpperHalfPlane.I < R}
      n x w) :
    dist (halfPlaneCayley (x • UpperHalfPlane.I))
        (halfPlaneCayley (walkEndpoint s n x w • UpperHalfPlane.I)) ≤
      (n : ℝ) * (4 * Real.exp (finiteJumpLengthBound Γ UpperHalfPlane.I s) * Real.exp (-R)) := by
  induction n generalizing x with
  | zero => simp [walkEndpoint]
  | succ n ih =>
    rcases w with ⟨g, w⟩
    obtain ⟨hx, hw⟩ := hw
    have hr : R ≤ dist (x • UpperHalfPlane.I) UpperHalfPlane.I :=
      le_of_not_gt hx
    have hj : dist (x • UpperHalfPlane.I) ((x * g) • UpperHalfPlane.I) ≤
        finiteJumpLengthBound Γ UpperHalfPlane.I s := by
      rw [mul_smul]
      change dist ((x : SL(2, ℝ)) • UpperHalfPlane.I)
        ((x : SL(2, ℝ)) • ((g : Γ) • UpperHalfPlane.I)) ≤ _
      rw [dist_smul]
      exact dist_le_finiteJumpLengthBound Γ UpperHalfPlane.I s g.property
    have hb := (halfPlaneCayley_dist_le _ _ _ hj).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hr)) (by positivity))
    change dist _ (halfPlaneCayley (walkEndpoint s n (x * g) w • UpperHalfPlane.I)) ≤ _
    calc
      _ ≤ dist (halfPlaneCayley (x • UpperHalfPlane.I))
          (halfPlaneCayley ((x * g) • UpperHalfPlane.I)) +
          dist (halfPlaneCayley ((x * g) • UpperHalfPlane.I))
            (halfPlaneCayley (walkEndpoint s n (x * g) w • UpperHalfPlane.I)) := dist_triangle _ _ _
      _ ≤ (4 * Real.exp (finiteJumpLengthBound Γ UpperHalfPlane.I s) * Real.exp (-R)) +
          (n : ℝ) * (4 * Real.exp (finiteJumpLengthBound Γ UpperHalfPlane.I s) * Real.exp (-R)) :=
        add_le_add hb (ih (x * g) w hw)
      _ = _ := by push_cast; ring

/-- Separated disk endpoints force an exponential lower bound on the number
of steps of a path avoiding the radius-R ball. -/
theorem walkEndpoint_detour_length (Γ : Subgroup SL(2, ℝ))
    (s : Finset Γ) (R δ : ℝ) (n : ℕ) (x : Γ) (w : WalkWord s n)
    (hw : avoidsBefore s {g : Γ | dist (g • UpperHalfPlane.I) UpperHalfPlane.I < R}
      n x w)
    (hsep : δ ≤ dist (halfPlaneCayley (x • UpperHalfPlane.I))
      (halfPlaneCayley (walkEndpoint s n x w • UpperHalfPlane.I))) :
    δ / (4 * Real.exp (finiteJumpLengthBound Γ UpperHalfPlane.I s)) * Real.exp R ≤ (n : ℝ) := by
  have hb := hsep.trans (walkEndpoint_cayley_detour_bound Γ s R n x w hw)
  have he : Real.exp (-R) * Real.exp R = 1 := by rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos R).le
  have hp : 0 < 4 * Real.exp (finiteJumpLengthBound Γ UpperHalfPlane.I s) := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).mpr
  simpa only [mul_assoc, he, mul_one] using hm

/-- All killed transition coefficients below the geometric detour cutoff vanish. -/
theorem killedWeight_eq_zero_of_short_detour (Γ : Subgroup SL(2, ℝ))
    (s : Finset Γ) (μ : Γ → ℝ) (R δ : ℝ) (n : ℕ) (x y : Γ)
    (hsep : δ ≤ dist (halfPlaneCayley (x • UpperHalfPlane.I))
      (halfPlaneCayley (y • UpperHalfPlane.I)))
    (hn : (n : ℝ) < δ / (4 * Real.exp (finiteJumpLengthBound Γ UpperHalfPlane.I s)) * Real.exp R) :
    killedWeight s μ {g : Γ | dist (g • UpperHalfPlane.I) UpperHalfPlane.I < R} n x y = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  split_ifs with hw
  · have hl := walkEndpoint_detour_length Γ s R δ n x w hw.1 (by simpa [hw.2.1] using hsep)
    exact (not_lt_of_ge hl hn).elim
  · rfl

end Singularity
