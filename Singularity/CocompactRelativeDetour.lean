import Singularity.CocompactGreenLower
import Singularity.HyperbolicGreenDetour

/-!
# Relative detour estimates in the cocompact case

The absolute double-exponential detour estimate, divided by the proved coarse
exponential Green lower bound, gives a relative error smaller than any chosen
exponential rate when endpoint distance grows at most linearly in ball radius.
The distance restriction is explicit; this is not yet the full Ancona inequality.
-/

noncomputable section
open Filter
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- With bounded triangle excess and endpoint distance at most B R, detours
outside the radius-R ball contribute at most exp(-K R) of the full Green mass,
uniformly in the orbit center and the endpoints, for all sufficiently large R. -/
theorem cocompact_relative_green_detour (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D B K : ℝ) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ u x y : Γ,
      2 ≤ dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) →
      dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ B * R →
      dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
        dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
        dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} x y ≤
        Real.exp (-K * R) * walkGreen s μ x y := by
  obtain ⟨a, b, ha, hb, hlower⟩ := cocompact_walkGreen_exp_lower Γ s μ hpos hgen hgap
  obtain ⟨A, c, hA, hc, hdetour⟩ := killedGreen_hyperbolic_detour_decay_of_excess
    Γ s μ (fun g hg => (hpos g hg).le) hgap D
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
    (double_exponential_eventually_le (A / a) c (K + b * B) (div_pos hA ha) hc)
  refine ⟨R₀, ?_⟩
  intro R hR u x y hd hdiam hexcess
  have hl : a * Real.exp (-b * (B * R)) ≤ walkGreen s μ x y := by
    apply le_trans _ (hlower x y)
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hdiam (neg_nonpos.mpr hb.le))) ha.le
  calc
    _ ≤ A * Real.exp (-c * Real.exp R) := hdetour R u x y hd hexcess
    _ = a * ((A / a) * Real.exp (-c * Real.exp R)) := by field_simp
    _ ≤ a * Real.exp (-(K + b * B) * R) := mul_le_mul_of_nonneg_left (hR₀ R hR) ha.le
    _ = Real.exp (-K * R) * (a * Real.exp (-b * (B * R))) := by
      rw [mul_left_comm (Real.exp (-K * R)) a, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le

/-- Equivalently, the normalized detour Green function has a uniform
exponential upper bound under the same geometric restrictions. -/
theorem cocompact_detour_green_ratio (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D B K : ℝ) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ u x y : Γ,
      2 ≤ dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) →
      dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ B * R →
      dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
        dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
        dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} x y /
        walkGreen s μ x y ≤ Real.exp (-K * R) := by
  obtain ⟨R₀, hR₀⟩ := cocompact_relative_green_detour Γ s μ hpos hgen hgap D B K
  refine ⟨R₀, ?_⟩
  intro R hR u x y hd hdiam hexcess
  exact (div_le_iff₀ (walkGreen_pos s μ hpos hgen hgap x y)).mpr
    (hR₀ R hR u x y hd hdiam hexcess)

end Singularity
