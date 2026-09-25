import Singularity.SupportedL2
import Singularity.DominatedLimit
import Singularity.WeightedCauchySchwarz
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Counting-measure L² and coordinatewise dominated limits

We construct the isometric coordinate map to the sequence ℓ² space and transfer
its already proved dominated-convergence theorem to the actual Hilbert spaces
used by the Green separator identity.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Singularity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

omit [Countable X] in
/-- The square sum of the coordinates of a counting-measure L² vector converges. -/
theorem counting_square_summable (f : GroupL2 X) : Summable (fun x => ‖f x‖ ^ 2) := by
  have h := integrable_count_iff.mp ((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num))
  simpa only [norm_pow, norm_norm] using h

/-- The counting-measure L² norm is the usual square-sum norm. -/
theorem counting_norm_sq (f : GroupL2 X) : ‖f‖ ^ 2 = ∑' x, ‖f x‖ ^ 2 := by
  have hnorm : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂Measure.count := by
    simpa only [Lp.toLp_coeFn] using toL2_norm_sq (Lp.memLp f)
  rw [hnorm]
  simpa [measureReal_def] using integral_countable
    ((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num))

/-- The pointwise coordinates define the same ℓ² vector. -/
def countingSequence (f : GroupL2 X) : SequenceL2 X :=
  ⟨(f : X → ℂ), (memℓp_gen_iff (p := 2) (by norm_num)).mpr
    (by simpa using counting_square_summable f)⟩

omit [Countable X] in
theorem countingSequence_apply (f : GroupL2 X) (x : X) : countingSequence f x = f x := rfl

theorem countingSequence_norm (f : GroupL2 X) : ‖countingSequence f‖ = ‖f‖ := by
  have h : ‖countingSequence f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [sequenceL2_norm_sq, counting_norm_sq]
    rfl
  nlinarith [norm_nonneg (countingSequence f), norm_nonneg f]

/-- The coordinate map is linear and isometric, not just an identification of sets. -/
def countingSequenceIsometry : GroupL2 X →ₗᵢ[ℂ] SequenceL2 X where
  toFun := countingSequence
  map_add' := by
    intro f g
    ext x
    exact counting_add_apply f g x
  map_smul' := by
    intro c f
    ext x
    exact counting_smul_apply c f x
  norm_map' := countingSequence_norm

/-- A square-summable envelope supplies membership in the concrete counting L² space. -/
theorem mem_countingL2_of_bound {v : X → ℂ} {b : X → ℝ}
    (hb : Summable (fun x => b x ^ 2)) (hbound : ∀ x, ‖v x‖ ≤ b x) :
    MemLp v 2 Measure.count := by
  apply (memLp_two_iff_integrable_sq_norm (measurable_of_countable v).aestronglyMeasurable).mpr
  apply integrable_count_iff.mpr
  have hs : Summable (fun x => ‖v x‖ ^ 2) := hb.of_nonneg_of_le
    (fun x => sq_nonneg _) (fun x => pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2)
  simpa only [norm_pow, norm_norm] using hs

/-- Coordinatewise convergence under a square-summable envelope is strong L² convergence. -/
theorem countingL2_tendsto_of_dominated {α : Type*} {l : Filter α} [l.NeBot]
    {u : α → GroupL2 X} {v : GroupL2 X} {b : X → ℝ}
    (hb : Summable (fun x => b x ^ 2))
    (hbound : ∀ᶠ n in l, ∀ x, ‖u n x‖ ≤ b x)
    (hpoint : ∀ x, Tendsto (fun n => u n x) l (𝓝 (v x))) : Tendsto u l (𝓝 v) := by
  apply (countingSequenceIsometry (X := X)).isometry.tendsto_nhds_iff.mpr
  exact sequenceL2_tendsto_of_dominated hb hbound hpoint

/-- The dominated raw coordinate limit exists as a supported Hilbert-space vector. -/
theorem supportedL2_limit_exists (A : Set X) {α : Type*} {l : Filter α} [l.NeBot]
    {u : α → supportedL2 A} {v : X → ℂ} {b : X → ℝ}
    (hb : Summable (fun x => b x ^ 2))
    (hbound : ∀ᶠ n in l, ∀ x, ‖(u n : GroupL2 X) x‖ ≤ b x)
    (hpoint : ∀ x, Tendsto (fun n => (u n : GroupL2 X) x) l (𝓝 (v x))) :
    ∃ w : supportedL2 A, (∀ x, (w : GroupL2 X) x = v x) ∧ Tendsto u l (𝓝 w) := by
  have hvbound : ∀ x, ‖v x‖ ≤ b x := fun x =>
    le_of_tendsto (hpoint x).norm (hbound.mono (fun n hn => hn x))
  let w0 := (mem_countingL2_of_bound hb hvbound).toLp v
  have hw (x : X) : w0 x = v x :=
    Measure.ae_count_iff.mp (MemLp.coeFn_toLp (mem_countingL2_of_bound hb hvbound)) x
  have hzero (x : X) (hx : x ∉ A) : v x = 0 := by
    have h := hpoint x
    have he : (fun n => (u n : GroupL2 X) x) = fun _ => (0 : ℂ) :=
      funext (fun n => (u n).property x hx)
    rw [he] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  let w : supportedL2 A := ⟨w0, fun x hx => (hw x).trans (hzero x hx)⟩
  refine ⟨w, hw, ?_⟩
  apply (supportedInclusion A).isometry.tendsto_nhds_iff.mpr
  apply countingL2_tendsto_of_dominated hb hbound
  intro x
  change Tendsto (fun n => (u n : GroupL2 X) x) l (𝓝 (w0 x))
  rw [hw x]
  exact hpoint x

/-- Dominated convergence directly in the supported Hilbert space. -/
theorem supportedL2_tendsto_of_dominated (A : Set X) {α : Type*} {l : Filter α} [l.NeBot]
    {u : α → supportedL2 A} {v : supportedL2 A} {b : X → ℝ}
    (hb : Summable (fun x => b x ^ 2))
    (hbound : ∀ᶠ n in l, ∀ x, ‖(u n : GroupL2 X) x‖ ≤ b x)
    (hpoint : ∀ x, Tendsto (fun n => (u n : GroupL2 X) x) l (𝓝 ((v : GroupL2 X) x))) :
    Tendsto u l (𝓝 v) := by
  apply (supportedInclusion A).isometry.tendsto_nhds_iff.mpr
  exact countingL2_tendsto_of_dominated hb hbound hpoint

end Singularity
