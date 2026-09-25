import Singularity.KernelProjection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurable choice of unit kernel vectors

For a measurable family of bounded operators on a separable Hilbert space,
with nonzero kernel at every parameter, we construct a measurable unit vector
in that kernel. This includes the N × (N+1) frequency matrices in the proof.

The choice uses the first nonzero projection of a fixed countable dense sequence.
This avoids choosing a measurable eigenbasis or asserting that arbitrary choices
are measurable. No lower bound on a particular projection column is needed.
-/

noncomputable section
open TopologicalSpace MeasureTheory

namespace Singularity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [SecondCountableTopology E]

omit [CompleteSpace F] in
/-- Some vector in a fixed dense sequence has nonzero kernel projection. -/
theorem kernelProjection_denseSeq_nonzero (B : E →L[ℂ] F)
    (hker : ∃ v, v ≠ 0 ∧ B v = 0) :
    ∃ n : ℕ, kernelProjection B (denseSeq E n) ≠ 0 := by
  by_contra h
  push Not at h
  have heq : (kernelProjection B : E → E) = (fun _ : E => (0 : E)) :=
    (denseRange_denseSeq E).equalizer (kernelProjection B).continuous continuous_const
      (funext h)
  obtain ⟨v, hv, hBv⟩ := hker
  have hzero := congrFun heq v
  rw [kernelProjection_eq_self B hBv] at hzero
  exact hv hzero

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (E →L[ℂ] F)] [BorelSpace (E →L[ℂ] F)]
  {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable family with nontrivial kernels admits a measurable unit
kernel section. The proof applies even when the kernel dimension jumps. -/
theorem exists_measurable_unit_kernel {B : Ω → E →L[ℂ] F}
    (hB : Measurable B) (hker : ∀ ω, ∃ v, v ≠ 0 ∧ B ω v = 0) :
    ∃ v : Ω → E, Measurable v ∧ (∀ ω, ‖v ω‖ = 1) ∧ (∀ ω, B ω (v ω) = 0) := by
  classical
  let q : ℕ → Ω → E := fun n ω => kernelProjection (B ω) (denseSeq E n)
  have hq : ∀ n, Measurable (q n) := fun n =>
    measurable_kernelProjection_apply hB (denseSeq E n)
  have hex : ∀ ω, ∃ n, q n ω ≠ 0 := fun ω => kernelProjection_denseSeq_nonzero (B ω) (hker ω)
  let w : Ω → E := fun ω => q (Nat.find (hex ω)) ω
  have hw : Measurable w :=
    Measurable.find hq (fun n => (measurableSet_eq_fun (hq n) measurable_const).compl) hex
  have hw_ne (ω : Ω) : w ω ≠ 0 := Nat.find_spec (hex ω)
  have hw_ker (ω : Ω) : B ω (w ω) = 0 := kernelProjection_mem _ _
  let v : Ω → E := fun ω => ((‖w ω‖⁻¹ : ℝ) : ℂ) • w ω
  refine ⟨v, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.measurable.comp hw.norm.inv).smul hw
  · intro ω
    dsimp only [v]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hw_ne ω))]
  · intro ω
    dsimp only [v]
    rw [map_smul, hw_ker, smul_zero]

/-- Rank-nullity discharges the nonzero-kernel hypothesis for a measurable
family whose domain has strictly larger finite dimension than its codomain. -/
theorem exists_measurable_unit_kernel_of_finrank_lt
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (hdim : Module.finrank ℂ F < Module.finrank ℂ E)
    {B : Ω → E →L[ℂ] F} (hB : Measurable B) :
    ∃ v : Ω → E, Measurable v ∧ (∀ ω, ‖v ω‖ = 1) ∧ (∀ ω, B ω (v ω) = 0) := by
  apply exists_measurable_unit_kernel hB
  intro ω
  obtain ⟨v, hv, hn⟩ := (B ω).ker.ne_bot_iff.mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := (B ω).toLinearMap) hdim)
  exact ⟨v, hn, hv⟩

end Singularity
