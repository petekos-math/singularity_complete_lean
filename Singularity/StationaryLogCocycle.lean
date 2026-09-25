import Singularity.StationaryDensity
import Singularity.GreenDistance

/-!
# The logarithmic cocycle of an actual stationary measure

The inverse in the definition matches the usual Busemann convention:
sigma(gh,x) = sigma(g,hx) + sigma(h,x). The derivatives are those of actual
translated measures. Green bounds follow from optional stopping, without any
identification with a geometric Martin boundary.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical

namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B]

/-- The real logarithmic Radon–Nikodym cocycle, in the forward-action convention. -/
def stationaryLogCocycle (ν : Measure B) (g : Γ) (ξ : B) : ℝ :=
  -Real.log (stationaryRealDensity ν g⁻¹ ξ)

omit [MeasurableConstSMul Γ B] in
/-- Each group element defines a measurable real boundary function. -/
theorem measurable_stationaryLogCocycle (ν : Measure B) (g : Γ) :
    Measurable (stationaryLogCocycle ν g) :=
  ((measurable_stationaryDensity ν g⁻¹).ennreal_toReal.log).neg

variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (ν : Measure B) [IsFiniteMeasure ν]
  (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν)

include hpos hgen hstat in
/-- The real-valued derivatives satisfy the multiplicative cocycle identity. -/
theorem stationaryRealDensity_cocycle (g h : Γ) :
    ∀ᵐ ξ ∂ν, stationaryRealDensity ν (g * h) ξ =
      stationaryRealDensity ν g ξ * stationaryRealDensity ν h (g⁻¹ • ξ) := by
  filter_upwards [stationaryDensity_cocycle s μ hpos hgen ν hstat g h] with ξ hξ
  simpa only [stationaryRealDensity, ENNReal.toReal_mul] using congrArg ENNReal.toReal hξ

omit [MeasurableConstSMul Γ B] in
/-- The logarithmic cocycle is zero at the identity almost everywhere. -/
theorem stationaryLogCocycle_one : stationaryLogCocycle ν (1 : Γ) =ᵐ[ν] fun _ => 0 := by
  filter_upwards [stationaryDensity_one (Γ := Γ) ν] with ξ hξ
  simp only [stationaryLogCocycle, inv_one, stationaryRealDensity, hξ,
    ENNReal.toReal_one, Real.log_one, neg_zero]

include hpos hgen hstat in
/-- Exact additive cocycle identity, before choosing a common invariant conull set. -/
theorem stationaryLogCocycle_mul (g h : Γ) :
    ∀ᵐ ξ ∂ν, stationaryLogCocycle ν (g * h) ξ =
      stationaryLogCocycle ν g (h • ξ) + stationaryLogCocycle ν h ξ := by
  have hq : Measure.QuasiMeasurePreserving (fun ξ : B => h • ξ) ν ν :=
    ⟨measurable_const_smul h, (stationary_translate_equivalent s μ hpos hgen ν hstat h).1⟩
  filter_upwards [stationaryRealDensity_cocycle s μ hpos hgen ν hstat h⁻¹ g⁻¹,
    stationaryRealDensity_ae_harmonic s μ hpos hgen ν hstat,
    hq.ae (stationaryRealDensity_ae_harmonic s μ hpos hgen ν hstat)] with ξ hc hp hpg
  simp only [inv_inv] at hc
  simp only [stationaryLogCocycle, mul_inv_rev, hc]
  rw [Real.log_mul (hp.2 h⁻¹).1.ne' (hpg.2 g⁻¹).1.ne']
  ring

include hpos hgen in
/-- A normalized positive superharmonic function has logarithm bounded by the
forward and backward Green distances. -/
theorem normalized_superharmonic_log_green_bounds
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (H : Γ → ℝ) (hp : ∀ g, 0 < H g) (h1 : H 1 = 1)
    (hh : ∀ x, ∑ g ∈ s, μ g * H (x * g) ≤ H x) (g : Γ) :
    -greenDistance s μ g 1 ≤ Real.log (H g) ∧ Real.log (H g) ≤ greenDistance s μ 1 g := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hG := walkGreen_pos s μ hpos hgen hgap 1 1
  have hforward := walkGreen_pos s μ hpos hgen hgap 1 g
  have hbackward := walkGreen_pos s μ hpos hgen hgap g 1
  have hu := walkGreen_superharmonic_bound s μ (fun g hg => (hpos g hg).le)
    hmass hgap H (fun g => (hp g).le) hh 1 g
  have hl := walkGreen_superharmonic_bound s μ (fun g hg => (hpos g hg).le)
    hmass hgap H (fun g => (hp g).le) hh g 1
  rw [walkGreen_diagonal_eq, h1, mul_one] at hu
  rw [h1, mul_one] at hl
  have hu' := Real.log_le_log (mul_pos hforward (hp g)) hu
  have hl' := Real.log_le_log hbackward hl
  rw [Real.log_mul hforward.ne' (hp g).ne'] at hu'
  rw [Real.log_mul hG.ne' (hp g).ne'] at hl'
  simp only [greenDistance, Real.log_div hforward.ne' hG.ne', Real.log_div hbackward.ne' hG.ne']
  constructor <;> linarith

include hpos hgen hstat in
/-- All group elements simultaneously satisfy the Green bounds, for almost
every boundary point of any finite stationary measure. -/
theorem stationaryLogCocycle_ae_green_bounds
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∀ᵐ ξ ∂ν, ∀ g : Γ,
      -greenDistance s μ g 1 ≤ stationaryLogCocycle ν g ξ ∧
        stationaryLogCocycle ν g ξ ≤ greenDistance s μ 1 g := by
  filter_upwards [stationaryRealDensity_ae_harmonic s μ hpos hgen ν hstat] with ξ hξ
  intro g
  have hb := normalized_superharmonic_log_green_bounds s μ hpos hgen hmass hgap
    (fun x => stationaryRealDensity ν x ξ) (fun x => (hξ.2 x).1) hξ.1
    (fun x => by rw [← Finset.sum_coe_sort s]; exact (hξ.2 x).2.ge) g⁻¹
  have hforward : greenDistance s μ 1 g⁻¹ = greenDistance s μ g 1 := by
    simpa only [mul_one, mul_inv_cancel] using (greenDistance_left s μ g 1 g⁻¹).symm
  have hbackward : greenDistance s μ g⁻¹ 1 = greenDistance s μ 1 g := by
    simpa only [mul_one, mul_inv_cancel] using (greenDistance_left s μ g g⁻¹ 1).symm
  rw [hforward, hbackward] at hb
  dsimp [stationaryLogCocycle]
  constructor <;> linarith [hb.1, hb.2]

end Singularity
