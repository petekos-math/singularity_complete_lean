import Singularity.EntranceRepresentation

/-!
# From entrance-kernel comparison to boundary Harnack comparison

A real L² harmonic function is the absolutely convergent entrance average of
its boundary values. Comparing two rows of the actual entrance kernel thus
compares every nonnegative boundary datum with the same constants. Geometric
estimates for those kernel rows are still needed for the nested domains.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ)

include hμ hmass hgap in
/-- Entrance averaging of real L² data is absolutely summable. -/
theorem firstEntrance_real_summable (f : Γ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) 2 Measure.count) (x : Γ) :
    Summable (fun a => firstEntranceKernel s μ A x a * f a) := by
  let v := hf.toLp (fun x => (f x : ℂ))
  have hv (a : Γ) : v a = (f a : ℂ) := Measure.ae_count_iff.mp (MemLp.coeFn_toLp hf) a
  have hh := (firstEntranceExtension_summable_norm s μ hμ hmass hgap A v x).of_norm
  apply Complex.summable_ofReal.mp
  simpa only [hv, Complex.ofReal_mul] using hh

include hμ hmass hgap in
/-- Exact real-valued entrance representation for L² harmonic functions. -/
theorem harmonic_real_eq_firstEntrance_tsum (f : Γ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) 2 Measure.count)
    (hharm : ∀ x, x ∉ A → f x = ∑ g ∈ s, μ g * f (x*g)) (x : Γ) :
    f x = ∑' a : Γ, firstEntranceKernel s μ A x a * f a := by
  let v := hf.toLp (fun x => (f x : ℂ))
  have hv (a : Γ) : v a = (f a : ℂ) := Measure.ae_count_iff.mp (MemLp.coeFn_toLp hf) a
  have hharm : ∀ a, a ∉ A → rightMarkov s μ v a = v a := by
    intro a ha
    rw [rightMarkov_apply]
    simp only [hv]
    have hh := congrArg (fun r : ℝ => (r : ℂ)) (hharm a ha)
    push_cast at hh
    exact hh.symm
  have he := congrArg (fun v : GroupL2 Γ => v x)
    (firstEntranceExtension_eq_of_harmonic s μ hμ hmass hgap A v hharm)
  rw [firstEntranceExtension_eq_tsum] at he
  simp only [hv, ← Complex.ofReal_mul, ← Complex.ofReal_tsum] at he
  exact (Complex.ofReal_injective he).symm

include hμ hmass hgap in
/-- Bounds on actual entrance-kernel rows transfer to all nonnegative boundary
data whose harmonic extension is L². -/
theorem harmonic_comparison_of_entrance_comparison (f : Γ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) 2 Measure.count)
    (hharm : ∀ x, x ∉ A → f x = ∑ g ∈ s, μ g * f (x*g))
    (hboundary : ∀ a ∈ A, 0 ≤ f a) (x o : Γ) (L U : ℝ)
    (hcompare : ∀ a ∈ A, L * firstEntranceKernel s μ A o a ≤ firstEntranceKernel s μ A x a ∧
      firstEntranceKernel s μ A x a ≤ U * firstEntranceKernel s μ A o a) :
    L * f o ≤ f x ∧ f x ≤ U * f o := by
  have hx := firstEntrance_real_summable s μ hμ hmass hgap A f hf x
  have ho := firstEntrance_real_summable s μ hμ hmass hgap A f hf o
  have hterm (a : Γ) :
      L * (firstEntranceKernel s μ A o a * f a) ≤ firstEntranceKernel s μ A x a * f a ∧
      firstEntranceKernel s μ A x a * f a ≤ U * (firstEntranceKernel s μ A o a * f a) := by
    by_cases ha : a ∈ A
    · have hh := hcompare a ha
      constructor
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh.1 (hboundary a ha)
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh.2 (hboundary a ha)
    · simp only [firstEntranceKernel_eq_zero_of_notMem s μ A _ a ha, zero_mul, mul_zero, le_refl, and_self]
  rw [harmonic_real_eq_firstEntrance_tsum s μ hμ hmass hgap A f hf hharm x,
    harmonic_real_eq_firstEntrance_tsum s μ hμ hmass hgap A f hf hharm o]
  constructor
  · rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun a => (hterm a).1) (ho.mul_left L) hx
  · rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun a => (hterm a).2) hx (ho.mul_left U)

include hμ hmass hgap in
/-- Normalizing at a positive base value gives the same relative row bounds. -/
theorem normalized_harmonic_comparison_of_entrance_comparison (f : Γ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) 2 Measure.count)
    (hharm : ∀ x, x ∉ A → f x = ∑ g ∈ s, μ g * f (x*g))
    (hboundary : ∀ a ∈ A, 0 ≤ f a) (x o : Γ) (ho : 0 < f o) (L U : ℝ)
    (hcompare : ∀ a ∈ A, L * firstEntranceKernel s μ A o a ≤ firstEntranceKernel s μ A x a ∧
      firstEntranceKernel s μ A x a ≤ U * firstEntranceKernel s μ A o a) :
    f x / f o ∈ Set.Icc L U := by
  obtain ⟨hlo,hhi⟩ := harmonic_comparison_of_entrance_comparison s μ hμ hmass hgap A f hf hharm hboundary x o L U hcompare
  exact ⟨(le_div_iff₀ ho).mpr hlo, (div_le_iff₀ ho).mpr hhi⟩

end Singularity
