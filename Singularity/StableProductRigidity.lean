import Singularity.ErgodicCesaro
import Singularity.StableCesaro
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Invariant-measure rigidity from one-sided absolute continuity

This is the abstract analytic part of the Hopf argument. The reference
probability is ergodic. Charts have asymptotic trajectories along their first
coordinate. A second invariant probability is absolutely continuous with
respect to chart products whose second marginals are absolutely continuous
with respect to the reference transverse marginals. The first marginals may
be arbitrary. Then the two probabilities coincide.

The geometric charts and the invariant probability lifted from the Naïm
current are not constructed in this file; they are explicit hypotheses.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Function
open scoped Topology

namespace Singularity

/-- Transfer a subsequential average basin through one stable product chart. -/
theorem stable_chart_birkhoffAverage_transfer {X A B : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace A] [MeasurableSpace B]
    (T : X → X) (hT : Measurable T) (f : X → ℝ)
    (hf : UniformContinuous f) (μ : Measure X)
    (α α' : Measure A) (β β' : Measure B)
    [NeZero α] [SFinite β] [SFinite β'] (hβ : β' ≪ β)
    (chart : A × B → X) (hchart : Measurable chart)
    (href : (α.prod β).map chart ≪ μ)
    (hstable : ∀ a a' b, Tendsto
      (fun n => dist (T^[n] (chart (a, b))) (T^[n] (chart (a', b)))) atTop (𝓝 0))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (c : ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c)) :
    ∀ᵐ x ∂(α'.prod β').map chart,
      Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c) := by
  have hset : MeasurableSet {x | Tendsto
      (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c)} :=
    measurableSet_tendsto _ (fun k => measurable_real_birkhoffAverage T hT f hf.continuous.measurable (ns k))
  apply (ae_map_iff hchart.aemeasurable hset).mpr
  apply ae_product_of_fibre_saturation α α' β β' hβ _ (hset.preimage hchart)
  · intro a a' b hb
    exact stable_birkhoffAverage_subsequence T f hf _ _ (hstable a a' b) ns hns c hb
  · exact ae_of_ae_map hchart.aemeasurable (href.ae_le hlim)

/-- Countably many stable product charts transfer every reference basin to the candidate law. -/
theorem stable_charts_birkhoffAverage_transfer {X A B I : Type*} [Countable I]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace A] [MeasurableSpace B]
    (T : X → X) (hT : Measurable T) (f : X → ℝ)
    (hf : UniformContinuous f) (μ ν : Measure X)
    (α α' : I → Measure A) (β β' : I → Measure B)
    [∀ i, NeZero (α i)] [∀ i, SFinite (β i)] [∀ i, SFinite (β' i)]
    (hβ : ∀ i, β' i ≪ β i)
    (chart : I → A × B → X) (hchart : ∀ i, Measurable (chart i))
    (href : ∀ i, ((α i).prod (β i)).map (chart i) ≪ μ)
    (hcover : ν ≪ Measure.sum (fun i => ((α' i).prod (β' i)).map (chart i)))
    (hstable : ∀ i a a' b, Tendsto
      (fun n => dist (T^[n] (chart i (a, b))) (T^[n] (chart i (a', b)))) atTop (𝓝 0))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (c : ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c)) :
    ∀ᵐ x ∂ν, Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c) := by
  apply hcover.ae_le
  apply ae_sum_iff.mpr
  intro i
  exact stable_chart_birkhoffAverage_transfer T hT f hf μ (α i) (α' i) (β i) (β' i)
    (hβ i) (chart i) (hchart i) (href i) (hstable i) ns hns c hlim

/-- The two invariant probabilities agree on bounded uniformly continuous observables. -/
theorem integral_eq_of_stable_product_charts {X A B I : Type*} [Countable I]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace A] [MeasurableSpace B]
    (T : X → X) (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic T μ) (hν : MeasurePreserving T ν ν)
    (α α' : I → Measure A) (β β' : I → Measure B)
    [∀ i, NeZero (α i)] [∀ i, SFinite (β i)] [∀ i, SFinite (β' i)]
    (hβ : ∀ i, β' i ≪ β i)
    (chart : I → A × B → X) (hchart : ∀ i, Measurable (chart i))
    (href : ∀ i, ((α i).prod (β i)).map (chart i) ≪ μ)
    (hcover : ν ≪ Measure.sum (fun i => ((α' i).prod (β' i)).map (chart i)))
    (hstable : ∀ i a a' b, Tendsto
      (fun n => dist (T^[n] (chart i (a, b))) (T^[n] (chart i (a', b)))) atTop (𝓝 0))
    (f : X → ℝ) (hf : UniformContinuous f) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C) : (∫ x, f x ∂ν) = ∫ x, f x ∂μ := by
  obtain ⟨ns, hns, hlim⟩ := ergodic_bounded_birkhoffAverage_subsequence μ T hμ
    f hf.continuous.measurable C hC hbound
  apply integral_eq_of_birkhoffAverage_subsequence ν T hν f hf.continuous.measurable
    C hC hbound ns hns.tendsto_atTop
  exact stable_charts_birkhoffAverage_transfer T hμ.1.measurable f hf μ ν α α' β β'
    hβ chart hchart href hcover hstable ns hns.tendsto_atTop _ hlim

/-- On a compact metric space the preceding one-sided chart hypothesis forces equality. -/
theorem invariant_probability_eq_of_stable_product_charts {X A B I : Type*} [Countable I]
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace A] [MeasurableSpace B]
    (T : X → X) (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic T μ) (hν : MeasurePreserving T ν ν)
    (α α' : I → Measure A) (β β' : I → Measure B)
    [∀ i, NeZero (α i)] [∀ i, SFinite (β i)] [∀ i, SFinite (β' i)]
    (hβ : ∀ i, β' i ≪ β i)
    (chart : I → A × B → X) (hchart : ∀ i, Measurable (chart i))
    (href : ∀ i, ((α i).prod (β i)).map (chart i) ≪ μ)
    (hcover : ν ≪ Measure.sum (fun i => ((α' i).prod (β' i)).map (chart i)))
    (hstable : ∀ i a a' b, Tendsto
      (fun n => dist (T^[n] (chart i (a, b))) (T^[n] (chart i (a', b)))) atTop (𝓝 0)) :
    ν = μ := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact integral_eq_of_stable_product_charts T μ ν hμ hν α α' β β' hβ chart hchart
    href hcover hstable f (CompactSpace.uniformContinuous_of_continuous f.continuous) ‖f‖ (norm_nonneg _) f.norm_coe_le_norm

end Singularity
