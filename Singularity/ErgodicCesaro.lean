import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Almost-everywhere subsequential ergodic averages

The Hilbert-space mean ergodic theorem gives a subsequence of the actual
pointwise Cesàro averages converging almost everywhere to a constant. This is
sufficient for the stable-leaf argument; no pointwise ergodic theorem is assumed.
-/

noncomputable section
open MeasureTheory Filter Function
open scoped Topology

namespace Singularity

/-- Representatives of Koopman averages agree almost everywhere with orbit averages. -/
theorem koopman_birkhoffAverage_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : Lp ℝ 2 μ) (n : ℕ) :
    (birkhoffAverage ℝ (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
      id n f : Lp ℝ 2 μ) =ᵐ[μ] birkhoffAverage ℝ T f n := by
  let U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
  have hi (k : ℕ) : (U^[k] f : Lp ℝ 2 μ) =ᵐ[μ] fun x => f (T^[k] x) := by
    change ((Lp.compMeasurePreserving T hT)^[k] f : Lp ℝ 2 μ) =ᵐ[μ] _
    rw [Lp.compMeasurePreserving_iterate]
    exact Lp.coeFn_compMeasurePreserving f (hT.iterate k)
  have hsum : (∑ k ∈ Finset.range n, U^[k] f : Lp ℝ 2 μ) =ᵐ[μ]
      fun x => ∑ k ∈ Finset.range n, f (T^[k] x) := by
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range n) (fun k => U^[k] f),
      ae_all_iff.mpr hi] with x hx hix
    simpa only [hix] using hx

  exact (Lp.coeFn_smul ((n : ℝ)⁻¹) (∑ k ∈ Finset.range n, U^[k] f)).trans
    (hsum.fun_comp fun r => (n : ℝ)⁻¹ • r)

/-- Ergodic orbit averages of an `L²` function have an a.e. constant subsequential limit. -/
theorem ergodic_birkhoffAverage_subsequence {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) (hT : Ergodic T μ) (f : Lp ℝ 2 μ) :
    ∃ c : ℝ, ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c) := by
  let U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := (Lp.compMeasurePreservingₗᵢ ℝ T hT.1).toContinuousLinearMap
  let v : U.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :=
    (U.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)).orthogonalProjectionOnto f
  have hv : U (v : Lp ℝ 2 μ) = v := v.property
  have hvcomp : (fun x => (v : Lp ℝ 2 μ) (T x)) =ᵐ[μ] (v : Lp ℝ 2 μ) := by
    have h := Lp.coeFn_compMeasurePreserving (v : Lp ℝ 2 μ) hT.1
    change (U (v : Lp ℝ 2 μ) : Lp ℝ 2 μ) =ᵐ[μ] _ at h
    rw [hv] at h
    exact h.symm
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae
    (Lp.aestronglyMeasurable (v : Lp ℝ 2 μ)) hvcomp
  have hlim := U.tendsto_birkhoffAverage_orthogonalProjection
    (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 2) ℝ T hT.1).norm_toContinuousLinearMap_le f
  obtain ⟨ns, hns, hconv⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  refine ⟨c, ns, hns, ?_⟩
  have heq : ∀ᵐ x ∂μ, ∀ n, (birkhoffAverage ℝ U id n f : Lp ℝ 2 μ) x =
      birkhoffAverage ℝ T f n x :=
    ae_all_iff.mpr (fun n => koopman_birkhoffAverage_ae μ T hT.1 f n)
  filter_upwards [hconv, hc, heq] with x hx hcx heqx
  change Tendsto (fun i => (birkhoffAverage ℝ U id (ns i) f : Lp ℝ 2 μ) x)
    atTop (𝓝 ((v : Lp ℝ 2 μ) x)) at hx
  simpa only [heqx, hcx, Function.const_apply] using hx

/-- The preceding subsequence theorem for an actual square-integrable function. -/
theorem ergodic_birkhoffAverage_subsequence_of_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) (hT : Ergodic T μ) (f : X → ℝ) (hf : MemLp f 2 μ) :
    ∃ c : ℝ, ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c) := by
  obtain ⟨c, ns, hns, hlim⟩ := ergodic_birkhoffAverage_subsequence μ T hT (hf.toLp f)
  have heq : ∀ᵐ x ∂μ, ∀ n, (hf.toLp f) (T^[n] x) = f (T^[n] x) :=
    ae_all_iff.mpr fun n => (hT.1.iterate n).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
  refine ⟨c, ns, hns, ?_⟩
  filter_upwards [hlim, heq] with x hx heqx
  simpa only [birkhoffAverage, birkhoffSum, heqx] using hx

/-- Measurability of real orbit averages. -/
theorem measurable_real_birkhoffAverage {X : Type*} [MeasurableSpace X]
    (T : X → X) (hT : Measurable T) (f : X → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffAverage ℝ T f n) := by
  unfold birkhoffAverage birkhoffSum
  exact (measurable_const : Measurable (fun _ : X => (n : ℝ)⁻¹)).smul (Finset.measurable_sum _ fun k _ => hf.comp (hT.iterate k))

/-- A global bound on the observable also bounds every average, including the zeroth. -/
theorem norm_real_birkhoffAverage_le {X : Type*} (T : X → X) (f : X → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C) (n : ℕ) (x : X) :
    ‖birkhoffAverage ℝ T f n x‖ ≤ C := by
  by_cases hn : n = 0
  · simpa [hn] using hC
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc
    ‖birkhoffAverage ℝ T f n x‖ = (n : ℝ)⁻¹ * ‖∑ k ∈ Finset.range n, f (T^[k] x)‖ := by
      simp [birkhoffAverage, birkhoffSum]
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ‖f (T^[k] x)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn'.le)
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => hf _) (inv_nonneg.mpr hn'.le)
    _ = C := by simp [hn'.ne']

/-- An invariant finite measure integrates each nonempty orbit average to the original integral. -/
theorem integral_real_birkhoffAverage {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : Integrable f μ) (n : ℕ) (hn : n ≠ 0) :
    (∫ x, birkhoffAverage ℝ T f n x ∂μ) = ∫ x, f x ∂μ := by
  have hi (k : ℕ) : Integrable (fun x => f (T^[k] x)) μ :=
    ((hT.iterate k).integrable_comp hf.aestronglyMeasurable).mpr hf
  have he (k : ℕ) : (∫ x, f (T^[k] x) ∂μ) = ∫ x, f x ∂μ := by
    have hm : AEStronglyMeasurable f (μ.map T^[k]) := by
      rw [(hT.iterate k).map_eq]
      exact hf.aestronglyMeasurable
    rw [← integral_map (hT.iterate k).measurable.aemeasurable hm, (hT.iterate k).map_eq]
  simp only [birkhoffAverage, birkhoffSum]
  rw [integral_smul, integral_finsetSum _ (fun k _ => hi k)]
  simp [he, smul_eq_mul, Nat.cast_ne_zero.mpr hn]

/-- An a.e. subsequential average limit determines the integral for an invariant probability. -/
theorem integral_eq_of_birkhoffAverage_subsequence {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (f : X → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) (c : ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c)) :
    (∫ x, f x ∂μ) = c := by
  have hfi : Integrable f μ := Integrable.mono' (integrable_const C)
    hf.aestronglyMeasurable (Eventually.of_forall hbound)
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : X => C)
    (fun k => (measurable_real_birkhoffAverage T hT.measurable f hf (ns k)).aestronglyMeasurable)
    (integrable_const C)
    (fun k => Eventually.of_forall (norm_real_birkhoffAverage_le T f C hC hbound (ns k))) hlim
  have heq : (fun k => ∫ x, birkhoffAverage ℝ T f (ns k) x ∂μ) =ᶠ[atTop]
      fun _ => ∫ x, f x ∂μ := by
    filter_upwards [hns.eventually (eventually_ne_atTop 0)] with k hk
    exact integral_real_birkhoffAverage μ T hT f hfi (ns k) hk
  have hconv' : Tendsto (fun _ : ℕ => ∫ x, f x ∂μ) atTop (𝓝 c) := by
    simpa using hconv.congr' heq
  exact tendsto_nhds_unique tendsto_const_nhds hconv'

/-- An ergodic invariant probability supplies subsequential convergence to its space average. -/
theorem ergodic_bounded_birkhoffAverage_subsequence {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Ergodic T μ)
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ,
      Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨c, ns, hns, hlim⟩ := ergodic_birkhoffAverage_subsequence_of_memLp μ T hT f
    (MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hbound))
  have hc := integral_eq_of_birkhoffAverage_subsequence μ T hT.1 f hf C hC hbound
    ns hns.tendsto_atTop c hlim
  exact ⟨ns, hns, hc.symm ▸ hlim⟩

end Singularity
