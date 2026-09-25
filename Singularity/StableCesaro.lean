import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Cesàro limits along asymptotic trajectories

Uniformly continuous observables have the same subsequential average limits
along asymptotic trajectories. A measurable property constant on entire
fibres transfers from a reference product measure to an arbitrary first
marginal and an absolutely continuous second marginal.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Function
open scoped Topology

namespace Singularity

/-- Uniform continuity takes asymptotic pairs to asymptotic observed values. -/
theorem observed_dist_tendsto_zero {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (f : X → Y) (hf : UniformContinuous f)
    (x y : ℕ → X) (hxy : Tendsto (fun n => dist (x n) (y n)) atTop (𝓝 0)) :
    Tendsto (fun n => dist (f (x n)) (f (y n))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp hf ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hxy δ hδ
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using
    hδf (by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hN n hn)

/-- Contracting trajectories have asymptotic Cesàro averages. -/
theorem stable_birkhoffAverage_dist_tendsto_zero {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (f : X → ℝ) (hf : UniformContinuous f) (x y : X)
    (hxy : Tendsto (fun n => dist (T^[n] x) (T^[n] y)) atTop (𝓝 0)) :
    Tendsto (fun n => dist (birkhoffAverage ℝ T f n x)
      (birkhoffAverage ℝ T f n y)) atTop (𝓝 0) := by
  have h := (observed_dist_tendsto_zero f hf _ _ hxy).cesaro
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => (dist_birkhoffAverage_birkhoffAverage_le ℝ T f n x y).trans_eq ?_) h
  rw [div_eq_inv_mul]

/-- An average limit along a subsequence propagates to an asymptotic trajectory. -/
theorem stable_birkhoffAverage_subsequence {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (f : X → ℝ) (hf : UniformContinuous f) (x y : X)
    (hxy : Tendsto (fun n => dist (T^[n] x) (T^[n] y)) atTop (𝓝 0))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (c : ℝ)
    (hx : Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c)) :
    Tendsto (fun k => birkhoffAverage ℝ T f (ns k) y) atTop (𝓝 c) := by
  exact tendsto_of_tendsto_of_dist hx
    ((stable_birkhoffAverage_dist_tendsto_zero T f hf x y hxy).comp hns)

/-- Asymptotic observed values have asymptotic averages, without a metric on the state space. -/
theorem birkhoffAverage_sub_tendsto_zero_of_observed {X : Type*}
    (T : X → X) (f : X → ℝ) (x y : X)
    (hxy : Tendsto (fun n => f (T^[n] x) - f (T^[n] y)) atTop (𝓝 0)) :
    Tendsto (fun n => birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T f n y)
      atTop (𝓝 0) := by
  simpa only [birkhoffAverage, birkhoffSum, smul_eq_mul, Finset.sum_sub_distrib,
    mul_sub] using hxy.cesaro

/-- An average limit propagates whenever the observed orbit differences vanish. -/
theorem birkhoffAverage_subsequence_of_observed {X : Type*}
    (T : X → X) (f : X → ℝ) (x y : X)
    (hxy : Tendsto (fun n => f (T^[n] x) - f (T^[n] y)) atTop (𝓝 0))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (c : ℝ)
    (hx : Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c)) :
    Tendsto (fun k => birkhoffAverage ℝ T f (ns k) y) atTop (𝓝 c) := by
  have h := (birkhoffAverage_sub_tendsto_zero_of_observed T f x y hxy).comp hns
  simpa only [Function.comp_def, sub_sub_cancel, sub_zero] using hx.sub h

/-- Fubini and saturation in the first coordinate allow an arbitrary first marginal. -/
theorem ae_product_of_fibre_saturation {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (α α' : Measure A) (β β' : Measure B)
    [NeZero α] [SFinite β] [SFinite β'] (hβ : β' ≪ β)
    (P : A × B → Prop) (hP : MeasurableSet {p | P p})
    (hsat : ∀ a a' b, P (a, b) → P (a', b))
    (h : ∀ᵐ p ∂α.prod β, P p) : ∀ᵐ p ∂α'.prod β', P p := by
  obtain ⟨a, ha⟩ := (ae_ae_of_ae_prod h).exists
  apply (ae_prod_iff_ae_ae hP).mpr
  have ha' : ∀ᵐ b ∂β', P (a, b) := hβ.ae_le ha
  exact Eventually.of_forall fun a' => ha'.mono (fun b hb => hsat a a' b hb)

end Singularity
