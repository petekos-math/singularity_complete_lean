import Singularity.GreenSeparator

/-!
# Finite first-entrance decomposition of the Green kernel

For a finite set the supported Hilbert-space vector has its exact finite
point-mass expansion. This turns the already proved operator renewal formula
into a scalar sum over actual first-entrance probabilities.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace Singularity

/-- Every vector supported on a finite set is the sum of its point-mass coordinates. -/
theorem supportedL2_eq_sum_delta {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Finset X) (u : supportedL2 (A : Set X)) :
    u = ∑ a : A, (u : GroupL2 X) a • supportedDelta (A : Set X) a := by
  apply Subtype.ext
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro x
  have he : ((∑ a : A, (u : GroupL2 X) a • supportedDelta (A : Set X) a :
      supportedL2 (A : Set X)) : GroupL2 X) x =
      ∑ a : A, (u : GroupL2 X) a * (if x = (a : X) then 1 else 0) := by
    rw [← countingEvaluation_apply x]
    change ((countingEvaluation x).comp (supportedInclusion (A : Set X)).toContinuousLinearMap)
      (∑ a : A, (u : GroupL2 X) a • supportedDelta (A : Set X) a) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul]
    simp only [ContinuousLinearMap.comp_apply, countingEvaluation_apply, smul_eq_mul]
    change (u : GroupL2 X) a * countingDelta (a : X) x = _
    rw [countingDelta_apply]
  rw [he]
  by_cases hx : x ∈ A
  · rw [Finset.sum_eq_single (⟨x, hx⟩ : A)]
    · simp
    · intro b _ hb
      have hxb : x ≠ (b : X) := by
        intro he
        exact hb (Subtype.ext he.symm)
      simp [hxb]
    · simp
  · rw [u.property x hx]
    symm
    apply Finset.sum_eq_zero
    intro a _
    have hxa : x ≠ (a : X) := fun he => hx (he ▸ a.property)
    simp [hxa]

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- A finite first-entrance operator acts by its actual path-counting kernel. -/
theorem entranceOperator_finite_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ)
    (u : supportedL2 (A : Set Γ)) (x : Γ) :
    entranceOperator s μ hμ hmass hgap (A : Set Γ) u x =
      ∑ a : A, (u : GroupL2 Γ) a * (firstEntranceKernel s μ (A : Set Γ) x a : ℂ) := by
  have he := supportedL2_eq_sum_delta A u
  conv_lhs => rw [he]
  rw [map_sum, ← countingEvaluation_apply x]
  change countingEvaluation x (∑ a : A, entranceOperator s μ hμ hmass hgap (A : Set Γ)
    ((u : GroupL2 Γ) a • supportedDelta (A : Set Γ) a)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, map_smul]
  simp only [countingEvaluation_apply, smul_eq_mul, entranceOperator_coefficient]

/-- The exact finite scalar first-entrance decomposition. -/
theorem walkGreen_finite_entrance_decomposition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x y : Γ) :
    walkGreen s μ x y = killedGreen s μ (A : Set Γ) x y +
      ∑ a : A, firstEntranceKernel s μ (A : Set Γ) x a * walkGreen s μ a y := by
  have h := walkGreen_entrance_decomposition s μ hμ hmass hgap (A : Set Γ) x y
  rw [entranceOperator_finite_apply] at h
  simp_rw [supportedRestriction_apply, ← walkGreen_eq_coefficient s μ hgap] at h
  apply Complex.ofReal_injective
  push_cast
  simpa only [mul_comm] using h

/-- Stopping on a finite set can only decrease the Green mass at a target. -/
theorem finite_entrance_green_sum_le (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x y : Γ) :
    (∑ a : A, firstEntranceKernel s μ (A : Set Γ) x a * walkGreen s μ a y) ≤ walkGreen s μ x y := by
  rw [walkGreen_finite_entrance_decomposition s μ hμ hmass hgap A x y]
  exact le_add_of_nonneg_left (killedGreen_nonneg s μ hμ (A : Set Γ) x y)

end Singularity
