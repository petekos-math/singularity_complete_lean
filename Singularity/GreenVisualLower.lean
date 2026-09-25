import Singularity.GreenMartinLower
import Singularity.HittingMartinBounds
import Singularity.GreenVisualUpper

/-!
# Sharp lower Green decay from bounded visual densities

A suitable Martin point has G(1,x)K(x,p) bounded below. The actual hitting
derivative identification and visual bounds give K(x,p) ≤ (b/a)exp(d(i,xi)).
Combining them proves the missing lower estimate with exponent exactly one.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped Classical ENNReal Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

include horbit

/-- Two-sided visual bounds for the actual hitting measure imply the sharp
lower Green comparison at every pair of vertices. -/
theorem geometricHittingMeasure_implies_Green_lower (z : ℍ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlow : ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I ≤
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z)
    (hupp : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≤
      ENNReal.ofReal b • compactPoissonMeasure UpperHalfPlane.I) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : Γ,
      c * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) ≤ walkGreen s μ x y := by
  obtain ⟨C, hC, hmartin⟩ := cocompact_exists_martin_green_lower Γ s μ hpos hmass hgen hgap
  let c := a / (C * b)
  have hc : 0 < c := div_pos ha (mul_pos hC hb)
  have hbase (x : Γ) : c * Real.exp (-dist UpperHalfPlane.I (x • UpperHalfPlane.I)) ≤ walkGreen s μ 1 x := by
    obtain ⟨H, hH⟩ := hmartin x
    obtain ⟨p, hp⟩ := compactMartinPoint_surjective Γ s μ hpos hmass hgen hgap horbit H
    have hK := compactMartinPoint_le_exp_of_visual_bounds Γ s μ hpos hmass hgen hgap horbit z
      a b ha hb.le hlow hupp x p
    rw [hp] at hK
    have hG := (walkGreen_pos s μ hpos hgen hgap 1 x).le
    have ht := hH.trans (mul_le_mul_of_nonneg_left hK hG)
    have hm := mul_le_mul_of_nonneg_left ht (mul_pos hC ha).le
    have he₁ : (C * a) * (1 / C) = a := by field_simp
    have he₂ : (C * a) * (walkGreen s μ 1 x * ((b / a) *
        Real.exp (dist UpperHalfPlane.I (x • UpperHalfPlane.I)))) =
        (C * b) * (walkGreen s μ 1 x * Real.exp (dist UpperHalfPlane.I (x • UpperHalfPlane.I))) := by
      field_simp
    rw [he₁, he₂] at hm
    have hce : c ≤ walkGreen s μ 1 x * Real.exp (dist UpperHalfPlane.I (x • UpperHalfPlane.I)) :=
      (div_le_iff₀ (mul_pos hC hb)).mpr (by simpa only [mul_comm (C*b)] using hm)
    have hf := mul_le_mul_of_nonneg_right hce
      (Real.exp_pos (-dist UpperHalfPlane.I (x • UpperHalfPlane.I))).le
    simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using hf
  refine ⟨c, hc, fun x y => ?_⟩
  have h := hbase (x⁻¹ * y)
  have hg : walkGreen s μ 1 (x⁻¹ * y) = walkGreen s μ x y := by
    simpa only [mul_one, mul_inv_cancel_left] using (walkGreen_left s μ x 1 (x⁻¹ * y)).symm
  have hd : dist UpperHalfPlane.I ((x⁻¹ * y) • UpperHalfPlane.I) =
      dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) := by
    rw [← dist_smul (x : SL(2, ℝ)) UpperHalfPlane.I ((x⁻¹ * y) • UpperHalfPlane.I)]
    change dist (x • UpperHalfPlane.I) (x • ((x⁻¹ * y) • UpperHalfPlane.I)) = _
    rw [← mul_smul, mul_inv_cancel_left]
  rwa [hg, hd] at h

/-- The full sharp comparison follows from visual bounds, with a single
constant for both the original and reflected Green kernels. -/
theorem geometricHittingMeasure_implies_Green_comparison (z : ℍ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlow : ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I ≤
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z)
    (hupp : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≤
      ENNReal.ofReal b • compactPoissonMeasure UpperHalfPlane.I) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x y : Γ,
      (C⁻¹ * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) ≤ walkGreen s μ x y ∧
        walkGreen s μ x y ≤ C * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I))) ∧
      (C⁻¹ * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) ≤
          walkGreen (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) x y ∧
        walkGreen (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) x y ≤
          C * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I))) := by
  obtain ⟨c, hc, hl⟩ := geometricHittingMeasure_implies_Green_lower Γ s μ hpos hmass hgen hgap horbit z
    a b ha hb hlow hupp
  let C := max 1 (max c⁻¹ (2 * b * walkGreen s μ 1 1 / a))
  have hC : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hcC : c⁻¹ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hi : C⁻¹ ≤ c := by
    have h := inv_le_inv₀ hCpos (inv_pos.mpr hc)
    have hh := h.mpr hcC
    simpa only [inv_inv] using hh
  have hf (x y : Γ) :
      C⁻¹ * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) ≤ walkGreen s μ x y ∧
      walkGreen s μ x y ≤ C * Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) := by
    constructor
    · exact (mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le).trans (hl x y)
    · exact (geometricHittingMeasure_implies_Green_upper Γ s μ hpos hmass hgen hgap z
        a b ha hb.le hlow hupp x y).trans
        (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_pos _).le)
  refine ⟨C, hC, fun x y => ⟨hf x y, ?_⟩⟩
  rw [reflected_walkGreen s μ hgap]
  simpa only [dist_comm] using hf y x

end Singularity
