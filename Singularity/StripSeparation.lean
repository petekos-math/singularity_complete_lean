import Singularity.PeriodicStrip
import Singularity.GreenSeparator

/-!
# A geometric strip separates bounded-jump paths

The strip threshold sinh(L/2)+1 prevents a jump of hyperbolic length at most L
from connecting its two exterior sides. This gives the actual finite-path
separation predicate used in the Green-kernel factorization.
-/

noncomputable section
open Set
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- A convenient positive strip threshold for jumps of length at most L. -/
def jumpStripRadius (L : ℝ) : ℝ := Real.sinh (L / 2) + 1

/-- The chosen radius is positive whenever the jump bound is nonnegative. -/
theorem jumpStripRadius_pos {L : ℝ} (hL : 0 ≤ L) : 0 < jumpStripRadius L := by
  have hs : 0 ≤ Real.sinh (L / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
  unfold jumpStripRadius
  linarith

/-- Points beyond opposite strip sides cannot be joined by a bounded jump. -/
theorem opposite_ratio_sides_dist_gt {L : ℝ} (hL : 0 ≤ L) (z w : ℍ)
    (hz : z.re / z.im < -jumpStripRadius L)
    (hw : jumpStripRadius L < w.re / w.im) : L < dist z w := by
  by_contra! hd
  have hs : 0 ≤ Real.sinh (L / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hroot : 0 ≤ Real.sqrt (z.im * w.im) := Real.sqrt_nonneg _
  have hroot2 : Real.sqrt (z.im * w.im) ^ 2 = z.im * w.im :=
    Real.sq_sqrt (mul_pos z.im_pos w.im_pos).le
  have ham : 2 * Real.sqrt (z.im * w.im) ≤ z.im + w.im := by
    nlinarith [sq_nonneg (z.im - w.im), z.im_pos, w.im_pos]
  have hdist := (UpperHalfPlane.dist_le_iff_le_sinh).mp hd
  have hden : 0 < 2 * Real.sqrt (z.im * w.im) := by
    positivity
  have hd' := (div_le_iff₀ hden).mp hdist
  have hgap : w.re - z.re ≤ dist (z : ℂ) (w : ℂ) := by
    have hb := Complex.abs_re_le_norm ((z : ℂ) - (w : ℂ))
    rw [Complex.sub_re] at hb
    calc
      w.re - z.re = -(z.re - w.re) := by ring
      _ ≤ |z.re - w.re| := neg_le_abs _
      _ ≤ ‖(z : ℂ) - (w : ℂ)‖ := hb
      _ = dist (z : ℂ) (w : ℂ) := (dist_eq_norm _ _).symm
  have hz' := (div_lt_iff₀ z.im_pos).mp hz
  have hw' := (lt_div_iff₀ w.im_pos).mp hw
  have hm := mul_le_mul_of_nonneg_left ham hs
  unfold jumpStripRadius at hz' hw'
  nlinarith [z.im_pos, w.im_pos]

/-- A path avoiding a set, including its final vertex, starts outside that set. -/
theorem avoidsBefore_start_not_mem {G : Type*} [Group G] (s : Finset G) (A : Set G)
    (n : ℕ) (x : G) (w : WalkWord s n) (havoid : avoidsBefore s A n x w)
    (hend : walkEndpoint s n x w ∉ A) : x ∉ A := by
  cases n with
  | zero => exact hend
  | succ n => exact havoid.1

/-- If each avoiding step preserves a side, so does every avoiding finite path. -/
theorem avoiding_walk_stays_in_side {G : Type*} [Group G] (s : Finset G) (A U : Set G)
    (hstep : ∀ (g t : G), t ∈ s → g ∉ A → g * t ∉ A → g ∈ U → g * t ∈ U)
    (n : ℕ) (x : G) (w : WalkWord s n) (hx : x ∈ U)
    (havoid : avoidsBefore s A n x w) (hend : walkEndpoint s n x w ∉ A) :
    walkEndpoint s n x w ∈ U := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
    exact ih (x * w.1) w.2
      (hstep x w.1 w.1.property havoid.1
        (avoidsBefore_start_not_mem s A n (x * w.1) w.2 havoid.2 hend) hx)
      havoid.2 hend

/-- The side-preservation criterion supplies the exact separator predicate. -/
theorem separatesJumpPaths_of_invariant_side {G : Type*} [Group G]
    (s : Finset G) (A U : Set G)
    (hstep : ∀ (g t : G), t ∈ s → g ∉ A → g * t ∉ A → g ∈ U → g * t ∈ U)
    (x y : G) (hx : x ∈ U) (hy : y ∉ U) : SeparatesJumpPaths s A x y := by
  intro n w h
  apply hy
  rw [← h.2.1]
  exact avoiding_walk_stays_in_side s A U hstep n x w hx h.1 (h.2.1 ▸ h.2.2)

/-- An avoiding jump of length at most L preserves the negative side. -/
theorem bounded_jump_preserves_negative_side {L : ℝ} (hL : 0 ≤ L) (z w : ℍ)
    (hd : dist z w ≤ L) (hzout : z ∉ axisRatioStrip (jumpStripRadius L))
    (hwout : w ∉ axisRatioStrip (jumpStripRadius L)) (hzneg : z.re < 0) : w.re < 0 := by
  by_contra! hwnonneg
  have hzratio : z.re / z.im < 0 := div_neg_of_neg_of_pos hzneg z.im_pos
  have hwratio : 0 ≤ w.re / w.im := div_nonneg hwnonneg w.im_pos.le
  change ¬ |z.re / z.im| ≤ jumpStripRadius L at hzout
  change ¬ |w.re / w.im| ≤ jumpStripRadius L at hwout
  rw [abs_of_neg hzratio, not_le] at hzout
  rw [abs_of_nonneg hwratio, not_le] at hwout
  exact (not_lt_of_ge hd) (opposite_ratio_sides_dist_gt hL z w (by linarith) hwout)

/-- The geometric coordinate strip separates actual subgroup jump paths. -/
theorem axisRatioStrip_separatesJumpPaths (Γ : Subgroup SL(2, ℝ)) (z : ℍ)
    (s : Finset Γ) {L : ℝ} (hL : 0 ≤ L)
    (hjump : ∀ t ∈ s, dist z (t • z) ≤ L) (x y : Γ)
    (hx : (x • z).re < 0) (hy : 0 ≤ (y • z).re) :
    SeparatesJumpPaths s {g : Γ | g • z ∈ axisRatioStrip (jumpStripRadius L)} x y := by
  apply separatesJumpPaths_of_invariant_side s _ {g : Γ | (g • z).re < 0} _ x y hx
    (not_lt.mpr hy)
  intro g t ht hg hgt hgn
  apply bounded_jump_preserves_negative_side hL (g • z) ((g * t) • z) _ hg hgt hgn
  rw [mul_smul]
  change dist ((g : SL(2, ℝ)) • z) ((g : SL(2, ℝ)) • (t • z)) ≤ L
  rw [dist_smul]
  exact hjump t ht

end Singularity
