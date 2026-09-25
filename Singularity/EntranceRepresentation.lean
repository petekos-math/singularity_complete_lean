import Singularity.CountingKernel
import Singularity.EntranceOperator

/-!
# Exact entrance representations for L² harmonic functions

The actual first-entrance kernel represents every L² function harmonic outside
A. All sums, including for an infinite boundary A, are absolutely convergent.
This is the domain-exit representation needed for harmonic subtraction in
boundary Harnack arguments; no boundary Harnack comparison is assumed proved.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

/-- A first entrance cannot occur at a vertex outside the entrance set. -/
theorem firstEntranceKernel_eq_zero_of_notMem {Γ : Type*} [Group Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x a : Γ) (ha : a ∉ A) :
    firstEntranceKernel s μ A x a = 0 := by
  simp [firstEntranceKernel, firstEntranceWeight, ha]

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ)

/-- Restrict boundary data and extend by the actual first-entrance operator. -/
def firstEntranceExtension : GroupL2 Γ →L[ℂ] GroupL2 Γ :=
  (entranceOperator s μ hμ hmass hgap A).comp (supportedRestriction A)

theorem firstEntranceExtension_coefficient (x a : Γ) :
    firstEntranceExtension s μ hμ hmass hgap A (countingDelta a) x =
      (firstEntranceKernel s μ A x a : ℂ) := by
  by_cases ha : a ∈ A
  · change entranceOperator s μ hμ hmass hgap A (supportedRestriction A (countingDelta a)) x = _
    rw [supportedRestriction_delta_mem A ⟨a, ha⟩, entranceOperator_coefficient]
  · change entranceOperator s μ hμ hmass hgap A (supportedRestriction A (countingDelta a)) x = _
    rw [supportedRestriction_delta_notMem A a ha, map_zero, firstEntranceKernel_eq_zero_of_notMem s μ A x a ha]
    simpa only [Complex.ofReal_zero, countingEvaluation_apply] using (countingEvaluation x).map_zero

include hμ hmass hgap in
/-- Absolute convergence of the first-entrance series against arbitrary L² data. -/
theorem firstEntranceExtension_summable_norm (f : GroupL2 Γ) (x : Γ) :
    Summable (fun a : Γ => ‖(firstEntranceKernel s μ A x a : ℂ) * f a‖) := by
  have hh := (counting_operator_kernel_summable (firstEntranceExtension s μ hμ hmass hgap A) f x).norm
  simpa only [firstEntranceExtension_coefficient] using hh

/-- Exact first-entrance expansion, valid for infinite A. -/
theorem firstEntranceExtension_eq_tsum (f : GroupL2 Γ) (x : Γ) :
    firstEntranceExtension s μ hμ hmass hgap A f x =
      ∑' a : Γ, (firstEntranceKernel s μ A x a : ℂ) * f a := by
  simpa only [firstEntranceExtension_coefficient] using
    counting_operator_eq_tsum (firstEntranceExtension s μ hμ hmass hgap A) f x

/-- Only the boundary coordinates contribute to the series. -/
theorem firstEntranceExtension_eq_tsum_subtype (f : GroupL2 Γ) (x : Γ) :
    firstEntranceExtension s μ hμ hmass hgap A f x =
      ∑' a : A, (firstEntranceKernel s μ A x a : ℂ) * f a := by
  rw [firstEntranceExtension_eq_tsum]
  symm
  apply tsum_subtype_eq_of_support_subset (f := fun a : Γ => (firstEntranceKernel s μ A x a : ℂ) * f a) (s := A)
  intro a ha
  by_contra hna
  exact ha (by simp [firstEntranceKernel_eq_zero_of_notMem s μ A x a hna])

omit [Countable Γ] in
/-- An L² harmonic function is uniquely determined by its entrance-boundary values. -/
theorem firstEntranceExtension_eq_of_harmonic (f : GroupL2 Γ)
    (hf : ∀ x, x ∉ A → rightMarkov s μ f x = f x) :
    firstEntranceExtension s μ hμ hmass hgap A f = f := by
  apply harmonic_eq_of_boundary_eq (rightMarkov s μ) (rightMarkov_contraction s μ hμ hmass) hgap A
  · intro x hx
    have hh := congrArg (fun v : supportedL2 A => (v : GroupL2 Γ) x)
      (entranceOperator_boundary s μ hμ hmass hgap A (supportedRestriction A f))
    rw [supportedRestriction_apply A _ ⟨x, hx⟩, supportedRestriction_apply A _ ⟨x, hx⟩] at hh
    exact hh
  · intro x hx
    exact entranceOperator_harmonic s μ hμ hmass hgap A (supportedRestriction A f) hx
  · exact hf

include hμ hmass hgap in
/-- The harmonic representation by actual first-entrance probabilities. -/
theorem harmonic_eq_firstEntrance_tsum (f : GroupL2 Γ)
    (hf : ∀ x, x ∉ A → rightMarkov s μ f x = f x) (x : Γ) :
    f x = ∑' a : A, (firstEntranceKernel s μ A x a : ℂ) * f a := by
  rw [← firstEntranceExtension_eq_tsum_subtype s μ hμ hmass hgap A f x,
    firstEntranceExtension_eq_of_harmonic s μ hμ hmass hgap A f hf]

end Singularity
