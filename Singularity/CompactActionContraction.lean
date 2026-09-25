import Singularity.StableCesaro
import Singularity.SLTwoHaar
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Contracting shears on compact spaces

Convergence of a group element to the identity moves every point of a compact
space by a uniformly vanishing amount. Applied to diagonal conjugates of a
lower shear, this proves asymptoticity of the corresponding forward orbits.
-/

noncomputable section
open Filter Function
open scoped Topology MatrixGroups

namespace Singularity

/-- Near-identity group elements move even varying points by a vanishing distance. -/
theorem compact_action_dist_tendsto_zero {G X : Type*}
    [Group G] [TopologicalSpace G]
    [PseudoMetricSpace X] [CompactSpace X] [MulAction G X] [ContinuousSMul G X]
    (g : ℕ → G) (hg : Tendsto g atTop (𝓝 1)) (x : ℕ → X) :
    Tendsto (fun n => dist (x n) (g n • x n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hh : ∀ᶠ a : G in 𝓝 1, ∀ y : X, y ∈ Set.univ → dist y (a • y) < ε := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro y _
    have hc : Continuous (fun p : G × X => dist p.2 (p.1 • p.2)) :=
      continuous_snd.dist (continuous_fst.smul continuous_snd)
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hg.eventually hh)
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hN n hn (x n) (Set.mem_univ _)

/-- Contraction by conjugation produces asymptotic trajectories in a compact action. -/
theorem compact_action_asymptotic_of_conjugates {G X : Type*}
    [Group G] [TopologicalSpace G]
    [PseudoMetricSpace X] [CompactSpace X] [MulAction G X] [ContinuousSMul G X]
    (a u : G) (hu : Tendsto (fun n : ℕ => a ^ n * u * (a ^ n)⁻¹) atTop (𝓝 1))
    (x : X) : Tendsto (fun n => dist ((fun y : X => a • y)^[n] x)
      ((fun y : X => a • y)^[n] (u • x))) atTop (𝓝 0) := by
  have h := compact_action_dist_tendsto_zero _ hu (fun n => a ^ n • x)
  simpa only [smul_iterate, mul_smul, inv_smul_smul] using h

/-- Lower-shear translates are forward-asymptotic under a positive diagonal time. -/
theorem compact_lowerShear_asymptotic {X : Type*}
    [PseudoMetricSpace X] [CompactSpace X]
    [MulAction SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X]
    (τ : ℝ) (hτ : 0 < τ) (u : ℝ) (x : X) :
    Tendsto (fun n => dist ((fun y : X => dilationMatrix τ • y)^[n] x)
      ((fun y : X => dilationMatrix τ • y)^[n] (lowerShearMatrix u • x))) atTop (𝓝 0) := by
  apply compact_action_asymptotic_of_conjugates (dilationMatrix τ) (lowerShearMatrix u)
  have he (n : ℕ) : dilationMatrix τ ^ n = dilationMatrix ((n : ℝ) * τ) := by
    simpa using (dilationMatrix_zpow τ (n : ℤ)).symm
  simpa only [he] using lowerShear_conjugates_tendsto_one τ u hτ

/-- Cesàro subsequential limits propagate along the actual contracting shear orbits. -/
theorem compact_lowerShear_birkhoffAverage_subsequence {X : Type*}
    [PseudoMetricSpace X] [CompactSpace X]
    [MulAction SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X]
    (τ : ℝ) (hτ : 0 < τ) (u : ℝ) (x : X) (f : X → ℝ) (hf : Continuous f)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (c : ℝ)
    (hx : Tendsto (fun k => birkhoffAverage ℝ (fun y : X => dilationMatrix τ • y)
      f (ns k) x) atTop (𝓝 c)) :
    Tendsto (fun k => birkhoffAverage ℝ (fun y : X => dilationMatrix τ • y)
      f (ns k) (lowerShearMatrix u • x)) atTop (𝓝 c) := by
  exact stable_birkhoffAverage_subsequence _ f
    (CompactSpace.uniformContinuous_of_continuous hf) _ _
    (compact_lowerShear_asymptotic τ hτ u x) ns hns c hx

/-- Continuous observables also detect uniform near-identity convergence on a compact
state space when no particular compatible metric has been selected. -/
theorem compact_action_observed_sub_tendsto_zero {G X : Type*}
    [Group G] [TopologicalSpace G] [TopologicalSpace X] [CompactSpace X]
    [MulAction G X] [ContinuousSMul G X]
    (g : ℕ → G) (hg : Tendsto g atTop (𝓝 1)) (x : ℕ → X)
    (f : X → ℝ) (hf : Continuous f) :
    Tendsto (fun n => f (x n) - f (g n • x n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hh : ∀ᶠ a : G in 𝓝 1, ∀ y : X, y ∈ Set.univ → ‖f y - f (a • y)‖ < ε := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro y _
    have hc : Continuous (fun p : G × X => ‖f p.2 - f (p.1 • p.2)‖) :=
      ((hf.comp continuous_snd).sub (hf.comp (continuous_fst.smul continuous_snd))).norm
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hg.eventually hh)
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using
    hN n hn (x n) (Set.mem_univ _)

/-- Contracting lower shears preserve every continuous observable's subsequential
Cesàro limit on a compact SL(2,ℝ) space, independently of a choice of metric. -/
theorem compact_lowerShear_average_limit {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    [MulAction SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X]
    (τ : ℝ) (hτ : 0 < τ) (u : ℝ) (x : X) (f : X → ℝ) (hf : Continuous f)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (c : ℝ)
    (hx : Tendsto (fun k => birkhoffAverage ℝ (fun y : X => dilationMatrix τ • y)
      f (ns k) x) atTop (𝓝 c)) :
    Tendsto (fun k => birkhoffAverage ℝ (fun y : X => dilationMatrix τ • y)
      f (ns k) (lowerShearMatrix u • x)) atTop (𝓝 c) := by
  apply birkhoffAverage_subsequence_of_observed _ f x _ _ ns hns c hx
  have h := compact_action_observed_sub_tendsto_zero _
    (lowerShear_conjugates_tendsto_one τ u hτ)
    (fun n : ℕ => dilationMatrix ((n : ℝ) * τ) • x) f hf
  have he (n : ℕ) : dilationMatrix τ ^ n = dilationMatrix ((n : ℝ) * τ) := by
    simpa using (dilationMatrix_zpow τ (n : ℤ)).symm
  simpa only [smul_iterate, he, mul_smul, inv_smul_smul] using h

end Singularity
