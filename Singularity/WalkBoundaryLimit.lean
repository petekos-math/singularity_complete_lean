import Singularity.WalkHeadTail
import Mathlib.Topology.Algebra.MulAction

/-!
# The first-step identity for path limits

A limit in any Hausdorff equivariant compactification obeys the boundary
cocycle relation almost surely. The proof uses the actual shifted infinite
walk, uniqueness of limits, and preservation of the path law by the shift.
Existence of convergence is an explicit input.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Removing the first jump leaves a walk starting at the identity, translated by that jump. -/
theorem walkPosition_first_step (s : Finset Γ) (n : ℕ) (ω : ℕ → s) :
    walkPosition s 1 (n + 1) ω = (ω 0 : Γ) *
      walkPosition s 1 n (fun k => ω (k + 1)) := by
  rw [walkPosition_succ, one_mul]
  simpa only [mul_one] using walkPosition_left s (ω 0 : Γ) 1 n (fun k => ω (k + 1))

/-- Splitting at any deterministic time gives the multiplicative path cocycle. -/
theorem walkPosition_add (s : Finset Γ) (x : Γ) (m n : ℕ) (ω : ℕ → s) :
    walkPosition s x (m + n) ω = walkPosition s x m ω *
      walkPosition s 1 n (fun k => ω (k + m)) := by
  induction m generalizing x ω with
  | zero =>
    simpa only [zero_add, Nat.add_zero, walkPosition_zero, mul_one] using
      walkPosition_left s x 1 n ω
  | succ m ih =>
    rw [Nat.succ_add, walkPosition_succ, walkPosition_succ, ih]
    congr 2

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
variable {B : Type*} [TopologicalSpace B] [T2Space B] [MulAction Γ B]
    [ContinuousConstSMul Γ B]

omit [MeasurableSingletonClass Γ] in
/-- Almost-sure convergence gives the first-step relation for the limiting point. -/
theorem walkBoundaryLimit_first_step (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (orbit : Γ → B) (horbit : ∀ g h, orbit (g * h) = g • orbit h)
    (b : (ℕ → s) → B)
    (hlimit : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds (b ω))) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      b ω = (ω 0 : Γ) • b (fun k => ω (k + 1)) := by
  have hshift : MeasurePreserving (fun (ω : ℕ → s) k => ω (k + 1))
      (infiniteWalkLaw s μ hμ hmass) (infiniteWalkLaw s μ hμ hmass) :=
    ⟨by fun_prop, infiniteWalkLaw_shift s μ hμ hmass 1⟩
  filter_upwards [hlimit, hshift.quasiMeasurePreserving.ae hlimit] with ω hω ht
  apply tendsto_nhds_unique (hω.comp (tendsto_add_atTop_nat 1))
  have hc := (continuous_const_smul (ω 0 : Γ)).continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, walkPosition_first_step, horbit] using hc

end Singularity
