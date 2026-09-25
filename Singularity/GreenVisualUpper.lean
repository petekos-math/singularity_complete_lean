import Singularity.GreenFirstHit
import Singularity.PoissonDominationDecay
import Singularity.GeometricHittingMeasure

/-!
# Upper Green decay from bounded visual densities

Two-sided domination of a stationary boundary probability by visual measure
implies G(x,y) ≤ C exp(-d(x i,y i)). The argument uses first-hit domination,
Poisson densities, and singleton Green renewal. No identification with Martin
kernels or full two-sided Green comparison is assumed.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ))
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ)
  (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hgen hgap

/-- Bounded visual density gives exponential decay of the singleton first-hit probability. -/
theorem firstEntrance_exp_bound_of_visual_bounds
    (ν : Measure (OnePoint ℝ)) [IsFiniteMeasure ν]
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : OnePoint ℝ => (g : Γ) • ξ) ν)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlow : ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I ≤ ν)
    (hupp : ν ≤ ENNReal.ofReal b • compactPoissonMeasure UpperHalfPlane.I) (y : Γ) :
    firstEntranceKernel s μ {y} 1 y * a ≤
      2 * b * Real.exp (-dist UpperHalfPlane.I (y • UpperHalfPlane.I)) := by
  let F := firstEntranceKernel s μ {y} 1 y
  have hF : 0 ≤ F := firstEntranceKernel_nonneg s μ (fun g hg => (hpos g hg).le) {y} 1 y
  have hd : ENNReal.ofReal F • Measure.map (fun ξ : OnePoint ℝ => y • ξ) ν ≤ ν := by
    have h := firstEntrance_stationary_measure_domination s μ hpos hgen hgap ν hstat 1 y
    have hid : (fun ξ : OnePoint ℝ => (1 : Γ) • ξ) = id := by
      funext ξ
      exact one_smul Γ ξ
    rw [hid, Measure.map_id] at h
    exact h
  have hy : ENNReal.ofReal a • compactPoissonMeasure (y • UpperHalfPlane.I) ≤
      Measure.map (fun ξ : OnePoint ℝ => y • ξ) ν := by
    have h := Measure.map_mono hlow (measurable_const_smul y)
    rw [Measure.map_smul _ (measurable_const_smul y).aemeasurable] at h
    change ENNReal.ofReal a • Measure.map (fun ξ : OnePoint ℝ => (y : SL(2, ℝ)) • ξ)
      (compactPoissonMeasure UpperHalfPlane.I) ≤ _ at h
    rwa [compactPoissonMeasure_covariance] at h
  apply compactPoisson_domination_exp_decay (y • UpperHalfPlane.I) (F * a) b (mul_nonneg hF ha.le) hb
  calc
    _ = ENNReal.ofReal F • (ENNReal.ofReal a • compactPoissonMeasure (y • UpperHalfPlane.I)) := by
      rw [ENNReal.ofReal_mul hF, smul_smul]
    _ ≤ ENNReal.ofReal F • Measure.map (fun ξ : OnePoint ℝ => y • ξ) ν := smul_le_smul_left _ hy
    _ ≤ ν := hd
    _ ≤ _ := hupp

include hmass

/-- The upper Green-distance estimate follows from two-sided visual measure bounds. -/
theorem walkGreen_exp_upper_of_visual_bounds
    (ν : Measure (OnePoint ℝ)) [IsFiniteMeasure ν]
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : OnePoint ℝ => (g : Γ) • ξ) ν)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlow : ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I ≤ ν)
    (hupp : ν ≤ ENNReal.ofReal b • compactPoissonMeasure UpperHalfPlane.I) (x y : Γ) :
    walkGreen s μ x y ≤ (2 * b * walkGreen s μ 1 1 / a) *
      Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  have hbase (g : Γ) : walkGreen s μ 1 g ≤ (2 * b * walkGreen s μ 1 1 / a) *
      Real.exp (-dist UpperHalfPlane.I (g • UpperHalfPlane.I)) := by
    have h := firstEntrance_exp_bound_of_visual_bounds Γ s μ hpos hgen hgap ν hstat a b ha hb hlow hupp g
    have hdiag : walkGreen s μ g g = walkGreen s μ 1 1 := by
      simpa only [mul_one] using walkGreen_left s μ g 1 1
    have hg := mul_le_mul_of_nonneg_left h (walkGreen_nonneg s μ hμ 1 1)
    rw [walkGreen_first_hit s μ hμ hmass hgap 1 g, hdiag]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    convert hg using 1 <;> ring
  have h := hbase (x⁻¹ * y)
  have hg : walkGreen s μ 1 (x⁻¹ * y) = walkGreen s μ x y := by
    simpa only [mul_one, mul_inv_cancel_left] using (walkGreen_left s μ x 1 (x⁻¹ * y)).symm
  have hd : dist UpperHalfPlane.I ((x⁻¹ * y) • UpperHalfPlane.I) =
      dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) := by
    rw [← dist_smul (x : SL(2, ℝ)) UpperHalfPlane.I ((x⁻¹ * y) • UpperHalfPlane.I)]
    change dist (x • UpperHalfPlane.I) (x • ((x⁻¹ * y) • UpperHalfPlane.I)) = _
    rw [← mul_smul, mul_inv_cancel_left]
  rwa [hg, hd] at h

/-- The bound applies to the constructed geometric hitting measure itself. -/
theorem geometricHittingMeasure_implies_Green_upper [DiscreteTopology Γ] (z : ℍ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlow : ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I ≤
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z)
    (hupp : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≤
      ENNReal.ofReal b • compactPoissonMeasure UpperHalfPlane.I) :
    ∀ x y : Γ, walkGreen s μ x y ≤ (2 * b * walkGreen s μ 1 1 / a) *
      Real.exp (-dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) := by
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact walkGreen_exp_upper_of_visual_bounds Γ s μ hpos hmass hgen hgap _
    (geometricHittingMeasure_stationary Γ s μ hpos hmass hgen hgap z) a b ha hb hlow hupp

end Singularity
