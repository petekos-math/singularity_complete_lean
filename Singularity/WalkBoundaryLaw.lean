import Singularity.WalkBoundaryLimit

/-!
# Boundary laws and their stationarity

A measurable path limit with the first-step equivariance relation has a
stationary pushforward law. The relation itself follows from almost-sure
convergence in a Hausdorff space with continuous group action. This file does
not assert existence of the geometric boundary limit.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace Singularity

variable {Γ : Type*} [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
variable {B : Type*} [MeasurableSpace B]

/-- The distribution of a measurable candidate boundary map. -/
def walkBoundaryLaw (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (b : (ℕ → s) → B) : Measure B :=
  Measure.map b (infiniteWalkLaw s μ hμ hmass)

omit [MeasurableSingletonClass Γ] in
/-- A measurable candidate boundary map has a probability distribution. -/
theorem walkBoundaryLaw_probability (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (b : (ℕ → s) → B) (hb : Measurable b) :
    IsProbabilityMeasure (walkBoundaryLaw s μ hμ hmass b) := by
  unfold walkBoundaryLaw
  exact (Measure.isProbabilityMeasure_map_iff hb.aemeasurable).mpr inferInstance

/-- A measurable function of head and tail has the finite mixture of its section laws. -/
theorem infiniteWalkLaw_head_tail_map (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (f : s × (ℕ → s) → B) (hf : Measurable f) :
    Measure.map (fun ω : ℕ → s => f (ω 0, fun n => ω (n + 1)))
      (infiniteWalkLaw s μ hμ hmass) =
      ∑ g : s, ENNReal.ofReal (μ g) •
        Measure.map (fun ω => f (g, ω)) (infiniteWalkLaw s μ hμ hmass) := by
  change Measure.map (f ∘ (fun ω : ℕ → s => (ω 0, fun n => ω (n + 1)))) _ = _
  rw [← Measure.map_map hf (by fun_prop), infiniteWalkLaw_head_tail]
  ext t ht
  rw [Measure.map_apply hf ht, Measure.prod_apply (ht.preimage hf), lintegral_fintype]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro g _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton g), supportJumpLaw_apply,
    Measure.map_apply (show Measurable (fun ω => f (g, ω)) from hf.comp measurable_prodMk_left) ht, mul_comm]
  rfl

variable [Group Γ] [MulAction Γ B] [MeasurableSMul₂ Γ B]

/-- The first-step boundary relation implies the stationary-measure equation. -/
theorem walkBoundaryLaw_stationary (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (b : (ℕ → s) → B) (hb : Measurable b)
    (hstep : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      b ω = (ω 0 : Γ) • b (fun n => ω (n + 1))) :
    walkBoundaryLaw s μ hμ hmass b =
      ∑ g : s, ENNReal.ofReal (μ g) •
        Measure.map (fun ξ : B => (g : Γ) • ξ) (walkBoundaryLaw s μ hμ hmass b) := by
  unfold walkBoundaryLaw
  nth_rw 1 [Measure.map_congr hstep]
  rw [infiniteWalkLaw_head_tail_map s μ hμ hmass
      (fun p : s × (ℕ → s) => (p.1 : Γ) • b p.2)
      ((measurable_subtype_coe.comp measurable_fst).smul (hb.comp measurable_snd))]
  apply Finset.sum_congr rfl
  intro g _
  rw [Measure.map_map (measurable_const_smul _) hb]
  rfl

/-- A measurable almost-sure path limit has a stationary law. -/
theorem walkBoundaryLaw_stationary_of_tendsto
    [TopologicalSpace B] [T2Space B] [ContinuousConstSMul Γ B]
    (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (orbit : Γ → B) (horbit : ∀ g h, orbit (g * h) = g • orbit h)
    (b : (ℕ → s) → B) (hb : Measurable b)
    (hlimit : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds (b ω))) :
    walkBoundaryLaw s μ hμ hmass b =
      ∑ g : s, ENNReal.ofReal (μ g) •
        Measure.map (fun ξ : B => (g : Γ) • ξ) (walkBoundaryLaw s μ hμ hmass b) :=
  walkBoundaryLaw_stationary s μ hμ hmass b hb
    (walkBoundaryLimit_first_step s μ hμ hmass orbit horbit b hlimit)

end Singularity
