import Singularity.AxisBallGeometry
import Singularity.ShrinkingAxisInterval

/-!
# Geometry of one shrinking-interval step

Admissible endpoints remain in tubes of radius one fiftieth of their respective
axis distance from zero, plus the fixed orbit-approximation error. A ball of
radius one four-hundredth of the interval length preserves this condition when
the longer side is halved. Every admissible pair has uniformly bounded triangle
excess at the new orbit center.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Tube of admissible endpoint pairs for an interval with left/right lengths p. -/
def axisPairSet (Γ : Subgroup SL(2, ℝ)) (g : SL(2, ℝ)) (E : ℝ) (p : ℝ × ℝ) :
    Set (Γ × Γ) :=
  {xy | dist (xy.1 • UpperHalfPlane.I) (g • verticalHeightRay UpperHalfPlane.I (-p.1)) ≤ p.1 / 50 + E ∧
    dist (xy.2 • UpperHalfPlane.I) (g • verticalHeightRay UpperHalfPlane.I p.2) ≤ p.2 / 50 + E}

/-- Moving into the next orbit ball preserves the admissible endpoint tubes. -/
theorem axisPairSet_step (Γ : Subgroup SL(2, ℝ)) (g : SL(2, ℝ))
    (E : ℝ) (p : ℝ × ℝ) (hl : 0 ≤ p.1) (_hr : 0 ≤ p.2) (u a : Γ)
    (hu : dist (u • UpperHalfPlane.I)
      (g • verticalHeightRay UpperHalfPlane.I (axisIntervalCut p)) ≤ E)
    (ha : dist (a • UpperHalfPlane.I) (u • UpperHalfPlane.I) < (p.1 + p.2) / 400)
    (xy : Γ × Γ) (hxy : xy ∈ axisPairSet Γ g E p) :
    (if axisIntervalLast p then (xy.1, a) else (a, xy.2)) ∈
      axisPairSet Γ g E (axisIntervalStep p) := by
  have hclose := (dist_triangle (a • UpperHalfPlane.I) (u • UpperHalfPlane.I)
    (g • verticalHeightRay UpperHalfPlane.I (axisIntervalCut p))).trans
    (add_le_add ha.le hu)
  change _ ∧ _ at hxy
  by_cases hp : p.2 ≤ p.1
  · simp only [axisIntervalLast, axisIntervalStep, ite_eq_left hp, Bool.false_eq_true,
      ↓reduceIte, axisPairSet, Set.mem_ofPred_eq]
    have hc : axisIntervalCut p = -(p.1 / 2) := by simp [axisIntervalCut, hp, neg_div]
    rw [hc] at hclose
    exact ⟨by linarith, hxy.2⟩
  · simp only [axisIntervalLast, axisIntervalStep, ite_eq_right hp, ↓reduceIte,
      axisPairSet, Set.mem_ofPred_eq]
    have hc : axisIntervalCut p = p.2 / 2 := by simp [axisIntervalCut, hp]
    rw [hc] at hclose
    exact ⟨hxy.1, by linarith⟩

/-- Every admissible pair satisfies the detour hypotheses at the cut center,
with a fixed diameter-to-radius ratio of 800. -/
theorem axisPairSet_step_geometry (Γ : Subgroup SL(2, ℝ)) (g : SL(2, ℝ))
    (E : ℝ) (hE : 0 ≤ E) (p : ℝ × ℝ) (hl : 0 ≤ p.1) (hr : 0 ≤ p.2)
    (hlarge : 400 * (E + Real.log 64 + 1) ≤ p.1 + p.2) (u : Γ)
    (hu : dist (u • UpperHalfPlane.I)
      (g • verticalHeightRay UpperHalfPlane.I (axisIntervalCut p)) ≤ E)
    (xy : Γ × Γ) (hxy : xy ∈ axisPairSet Γ g E p) :
    2 ≤ dist (xy.1 • UpperHalfPlane.I) (xy.2 • UpperHalfPlane.I) ∧
    dist (xy.1 • UpperHalfPlane.I) (xy.2 • UpperHalfPlane.I) ≤ 800 * ((p.1 + p.2) / 400) ∧
    dist (xy.1 • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
      dist (xy.2 • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
      dist (xy.1 • UpperHalfPlane.I) (xy.2 • UpperHalfPlane.I) ≤ 2 * Real.log 32 + 2 * E := by
  have hlog : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  change _ ∧ _ at hxy
  have hd := axis_nearby_distance_bounds g (-p.1) p.2 (p.1 / 50 + E) (p.2 / 50 + E)
    (xy.1 • UpperHalfPlane.I) (xy.2 • UpperHalfPlane.I) (by linarith) hxy.1 hxy.2
  refine ⟨by linarith [hd.1], by linarith [hd.2], ?_⟩
  apply axis_balls_excess_near_center g (-p.1) (axisIntervalCut p) p.2
    (p.1 / 50 + E) (p.2 / 50 + E) E
    (xy.1 • UpperHalfPlane.I) (xy.2 • UpperHalfPlane.I) (u • UpperHalfPlane.I)
  · unfold axisIntervalCut
    split <;> linarith
  · unfold axisIntervalCut
    split <;> linarith
  · exact hxy.1
  · exact hxy.2
  · unfold axisIntervalCut
    split <;> linarith
  · unfold axisIntervalCut
    split <;> linarith
  · simpa only [dist_comm] using hu

/-- At the stopping time, every left endpoint is uniformly close to any
chosen orbit point within E of axis parameter zero. -/
theorem axisPairSet_terminal (Γ : Subgroup SL(2, ℝ)) (g : SL(2, ℝ))
    (E T : ℝ) (p : ℝ × ℝ) (hl : 0 ≤ p.1) (hr : 0 ≤ p.2) (hsmall : p.1 + p.2 ≤ T)
    (o : Γ) (ho : dist (g • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ E)
    (xy : Γ × Γ) (hxy : xy ∈ axisPairSet Γ g E p) :
    dist (xy.1 • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ 2 * T + 2 * E := by
  have haxis : dist (g • verticalHeightRay UpperHalfPlane.I (-p.1))
      (g • UpperHalfPlane.I) = p.1 := by
    rw [dist_smul]
    simpa only [verticalHeightRay_zero, sub_zero, abs_neg, abs_of_nonneg hl] using
      verticalHeightRay_dist_eq UpperHalfPlane.I (-p.1) 0
  have hh := dist_triangle4 (xy.1 • UpperHalfPlane.I)
    (g • verticalHeightRay UpperHalfPlane.I (-p.1)) (g • UpperHalfPlane.I) (o • UpperHalfPlane.I)
  rw [haxis] at hh
  change _ ∧ _ at hxy
  linarith [hxy.1]

end Singularity
