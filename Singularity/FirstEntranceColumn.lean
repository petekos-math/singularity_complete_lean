import Singularity.FirstEntrance
import Singularity.SupportedL2

/-!
# First-entrance columns as actual ℓ² vectors

The already proved pointwise bound 0≤F(x,a)≤G(x,a) makes each first-entrance
column square-integrable. We prove its boundary values and harmonicity as
statements about the original counting-measure Markov operator.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- Domination by a resolvent column supplies square integrability. -/
theorem firstEntranceColumn_memLp (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (a : Γ) :
    MemLp (fun x => (firstEntranceKernel s μ A x a : ℂ)) 2 Measure.count := by
  apply (Lp.memLp (green (rightMarkov s μ) (countingDelta a))).mono
    (measurable_of_countable _).aestronglyMeasurable
  apply Measure.ae_count_iff.mpr
  intro x
  rw [← walkGreen_eq_coefficient s μ hgap]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (firstEntranceKernel_nonneg s μ hμ A x a),
    abs_of_nonneg (walkGreen_nonneg s μ hμ x a)]
  exact firstEntranceKernel_le_green s μ hμ hgap A x a

/-- The ℓ² vector with coordinates F(x,a). -/
def firstEntranceColumn (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (a : Γ) : GroupL2 Γ :=
  (firstEntranceColumn_memLp s μ hμ hgap A a).toLp (fun x => (firstEntranceKernel s μ A x a : ℂ))

/-- Pointwise identification, valid everywhere for counting measure. -/
theorem firstEntranceColumn_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (a x : Γ) :
    firstEntranceColumn s μ hμ hgap A a x = (firstEntranceKernel s μ A x a : ℂ) :=
  Measure.ae_count_iff.mp (MemLp.coeFn_toLp (firstEntranceColumn_memLp s μ hμ hgap A a)) x

/-- The first-entrance column takes point-mass boundary values on A. -/
theorem firstEntranceColumn_boundary (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (a : Γ) {x : Γ} (hx : x ∈ A) :
    firstEntranceColumn s μ hμ hgap A a x = countingDelta a x := by
  rw [firstEntranceColumn_apply, firstEntranceKernel_of_mem s μ A hx, countingDelta_apply]
  split_ifs <;> simp

/-- Exterior harmonicity is an equality for the actual bounded Markov operator. -/
theorem firstEntranceColumn_harmonic (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (a : Γ) {x : Γ} (hx : x ∉ A) :
    rightMarkov s μ (firstEntranceColumn s μ hμ hgap A a) x =
      firstEntranceColumn s μ hμ hgap A a x := by
  rw [rightMarkov_apply]
  simp_rw [firstEntranceColumn_apply]
  have h := congrArg Complex.ofReal (firstEntranceKernel_harmonic s μ hμ hgap A hx a)
  push_cast at h
  exact h.symm

end Singularity
