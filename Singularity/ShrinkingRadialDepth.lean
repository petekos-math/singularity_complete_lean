import Singularity.ShrinkingAxisGeometry
import Singularity.RadialGeodesicConvexity

/-!
# Radial depth along the constructed shrinking-ball sequence

The left and right interval lengths decrease separately. A common depth at
the original axis ends therefore controls the whole sequence by geodesic
convexity. An extra (l+r)/50+E buffer accounts for every admissible endpoint tube.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Each side of the shrinking interval remains below its initial length. -/
theorem axisInterval_components_le (l r : ℝ) (hl : 0 ≤ l) (hr : 0 ≤ r) (n : ℕ) :
    (axisInterval l r n).1 ≤ l ∧ (axisInterval l r n).2 ≤ r := by
  induction n with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ n ih =>
    have hn := axisInterval_nonneg l r hl hr n
    change (axisIntervalStep _).1 ≤ l ∧ (axisIntervalStep _).2 ≤ r
    unfold axisIntervalStep
    split <;> dsimp <;> constructor <;> linarith [ih.1,ih.2,hn.1,hn.2]

/-- The original endpoint depth, with the explicit tube allowance, keeps every
admissible pair of the shrinking construction above a fixed radial level. -/
theorem axisPairSet_radial_depth (Γ : Subgroup SL(2, ℝ)) (g q : SL(2, ℝ))
    (E l r a H : ℝ) (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hleft : a+H+(l+r)/50+E ≤ axisRadialCoordinate (q • (g • verticalHeightRay UpperHalfPlane.I (-l))))
    (hright : a+H+(l+r)/50+E ≤ axisRadialCoordinate (q • (g • verticalHeightRay UpperHalfPlane.I r)))
    (n : ℕ) (xy : Γ × Γ) (hxy : xy ∈ axisPairSet Γ g E (axisInterval l r n)) :
    a+H ≤ axisRadialCoordinate (q • (xy.1 • UpperHalfPlane.I)) ∧
      a+H ≤ axisRadialCoordinate (q • (xy.2 • UpperHalfPlane.I)) := by
  have hp := axisInterval_nonneg l r hl hr n
  have hple := axisInterval_components_le l r hl hr n
  have hsegment (t : ℝ) (ht : t ∈ Set.Icc (-l) r) :
      a+H+(l+r)/50+E ≤ axisRadialCoordinate (q • (g • verticalHeightRay UpperHalfPlane.I t)) := by
    rw [← mul_smul]
    exact axisRadialCoordinate_segment_lower (q*g) _ (-l) r t ht.1 ht.2
      (by simpa only [mul_smul] using hleft) (by simpa only [mul_smul] using hright)
  have hlower := hsegment (-(axisInterval l r n).1) ⟨by linarith [hple.1],by linarith [hp.1]⟩
  have hupper := hsegment (axisInterval l r n).2 ⟨by linarith [hp.2],hple.2⟩
  change _ ∧ _ at hxy
  have hd₁ := axisRadialCoordinate_dist_le (q • (xy.1 • UpperHalfPlane.I))
    (q • (g • verticalHeightRay UpperHalfPlane.I (-(axisInterval l r n).1)))
  have hd₂ := axisRadialCoordinate_dist_le (q • (xy.2 • UpperHalfPlane.I))
    (q • (g • verticalHeightRay UpperHalfPlane.I (axisInterval l r n).2))
  rw [dist_smul] at hd₁ hd₂
  have hb₁ := (abs_le.mp (hd₁.trans hxy.1)).1
  have hb₂ := (abs_le.mp (hd₂.trans hxy.2)).1
  constructor <;> linarith [hple.1,hple.2]

end Singularity
