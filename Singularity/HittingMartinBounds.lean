import Singularity.HittingMartinIdentification
import Singularity.VisualPoissonComparison

/-!
# Uniform bounds on the actual geometric Martin kernels from visual bounds

Two-sided visual measure bounds control every translated hitting measure.
The proved Martin density identity and full support then turn this measure
inequality into an everywhere bound on the continuous Martin coordinates.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical ENNReal Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- Two-sided visual bounds control translates by an explicit exponential factor. -/
theorem boundary_translate_le_of_visual_bounds (Γ : Subgroup SL(2, ℝ))
    (ν : Measure (OnePoint ℝ)) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlow : ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I ≤ ν)
    (hupp : ν ≤ ENNReal.ofReal b • compactPoissonMeasure UpperHalfPlane.I) (x : Γ) :
    Measure.map (fun p : OnePoint ℝ => x • p) ν ≤
      ENNReal.ofReal ((b / a) * Real.exp (dist UpperHalfPlane.I (x • UpperHalfPlane.I))) • ν := by
  let e := Real.exp (dist UpperHalfPlane.I (x • UpperHalfPlane.I))
  let C := (b / a) * e
  have hC : 0 ≤ C := mul_nonneg (div_nonneg hb ha.le) (Real.exp_pos _).le
  have he : C * a = b * e := by dsimp [C]; field_simp
  have hm := Measure.map_mono hupp (measurable_const_smul x)
  rw [Measure.map_smul _ (measurable_const_smul x).aemeasurable] at hm
  have hc : Measure.map (fun p : OnePoint ℝ => x • p) (compactPoissonMeasure UpperHalfPlane.I) =
      compactPoissonMeasure (x • UpperHalfPlane.I) := compactPoissonMeasure_covariance x UpperHalfPlane.I
  rw [hc] at hm
  calc
    _ ≤ ENNReal.ofReal b • compactPoissonMeasure (x • UpperHalfPlane.I) := hm
    _ ≤ ENNReal.ofReal b • (ENNReal.ofReal e • compactPoissonMeasure UpperHalfPlane.I) :=
      smul_le_smul_left _ (compactPoissonMeasure_le_exp_dist _)
    _ = ENNReal.ofReal C • (ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I) := by
      rw [smul_smul, smul_smul, ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul hC, he]
    _ ≤ _ := smul_le_smul_left _ hlow

/-- A continuous nonnegative density of a fully supported measure inherits
any constant measure domination everywhere. -/
theorem continuous_density_le_of_measure_bound {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [BorelSpace B] (ν : Measure B) [SigmaFinite ν]
    [Measure.IsOpenPosMeasure ν] (K : B → ℝ) (hK : Continuous K) (hp : ∀ p, 0 ≤ K p)
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ν.withDensity (fun p => ENNReal.ofReal (K p)) ≤ ENNReal.ofReal C • ν) :
    ∀ p, K p ≤ C := by
  rw [← withDensity_const] at hdom
  have hae := ae_le_of_forall_setLIntegral_le_of_sigmaFinite hK.measurable.ennreal_ofReal
    (g := fun _ => ENNReal.ofReal C)
    (fun E hE _ => by simpa only [withDensity_apply _ hE, Pi.mul_apply] using hdom E)
  have hr : ∀ᵐ p ∂ν, K p ≤ C := by
    filter_upwards [hae] with p hp'
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp'
    simpa only [Pi.mul_apply, ENNReal.toReal_ofReal (hp p), ENNReal.toReal_ofReal hC] using ht
  have hclosed : IsClosed {p | K p ≤ C} := isClosed_le hK continuous_const
  have hd := (Measure.dense_of_ae hr).closure_eq
  intro p
  exact hclosed.closure_subset (hd.symm ▸ mem_univ p)

/-- The actual compact Martin kernel has the sharp displacement upper bound
whenever the hitting measure has two-sided visual bounds. -/
theorem compactMartinPoint_le_exp_of_visual_bounds
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) (z : ℍ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlow : ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I ≤
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z)
    (hupp : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≤
      ENNReal.ofReal b • compactPoissonMeasure UpperHalfPlane.I) (x : Γ) (p : OnePoint ℝ) :
    (compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x ≤
      (b / a) * Real.exp (dist UpperHalfPlane.I (x • UpperHalfPlane.I)) := by
  let ν := geometricHittingMeasure Γ s μ hpos hmass hgen hgap z
  let : IsProbabilityMeasure ν := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  let : Measure.IsOpenPosMeasure (compactPoissonMeasure UpperHalfPlane.I) :=
    compactPoissonMeasure_isOpenPosMeasure _
  let : Measure.IsOpenPosMeasure (ENNReal.ofReal a • compactPoissonMeasure UpperHalfPlane.I) :=
    Measure.isOpenPosMeasure_smul _ (ne_of_gt (ENNReal.ofReal_pos.mpr ha))
  let : Measure.IsOpenPosMeasure ν := hlow.isOpenPosMeasure
  apply continuous_density_le_of_measure_bound ν _
    (continuous_compactMartinPoint_eval Γ s μ hpos hmass hgen hgap horbit x)
    (fun q => (martinBoundaryKernel_pos s μ hpos hgen hgap 1 x
      (compactMartinPoint Γ s μ hpos hgen hgap horbit q)).le) _
    (mul_nonneg (div_nonneg hb ha.le) (Real.exp_pos _).le) _ p
  rw [← geometricHittingMeasure_martin_withDensity_basepoint Γ s μ hpos hmass hgen hgap horbit z x]
  exact boundary_translate_le_of_visual_bounds Γ ν a b ha hb hlow hupp x

end Singularity
