import Singularity.RelativeGreenEntrance
import Singularity.FiniteLastEntrance

/-!
# Reflection of the killed Green kernel

Both killed columns vanish on the killing set. Pairing their exterior Green
equations and using P_check = P* proves transposition by reflection, without
assuming a symmetric law or a new spectral theorem for the killed operator.
-/

noncomputable section
open MeasureTheory
namespace Singularity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

omit [MeasurableSingletonClass X] in
/-- A zero boundary value removes that boundary from a counting-L² pairing. -/
theorem counting_inner_eq_of_eq_off_boundary (A : Set X) (u v w : GroupL2 X)
    (hu : ∀ x ∈ A, u x = 0) (hvw : ∀ x, x ∉ A → v x = w x) :
    inner ℂ u v = inner ℂ u w := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  apply Measure.ae_count_iff.mpr
  intro x
  dsimp only
  by_cases hx : x ∈ A
  · rw [hu x hx, inner_zero_left, inner_zero_left]
  · rw [hvw x hx]

/-- Dual exterior Green equations identify the two point-mass pairings. -/
theorem killed_columns_duality (P : GroupL2 X →L[ℂ] GroupL2 X) (A : Set X)
    (f h : GroupL2 X) (x y : X)
    (hfA : ∀ z ∈ A, f z = 0) (hhA : ∀ z ∈ A, h z = 0)
    (hf : ∀ z, z ∉ A → (f-P f) z = countingDelta y z)
    (hh : ∀ z, z ∉ A → (h-P.adjoint h) z = countingDelta x z) :
    f x = (starRingEnd ℂ) (h y) := by
  have hleft := counting_inner_eq_of_eq_off_boundary A h (f-P f) (countingDelta y) hhA hf
  have hright := counting_inner_eq_of_eq_off_boundary A f (h-P.adjoint h) (countingDelta x) hfA hh
  have hd : inner ℂ h (f-P f) = inner ℂ (h-P.adjoint h) f := by
    rw [inner_sub_right, inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
  have hr : inner ℂ (h-P.adjoint h) f = inner ℂ (countingDelta x) f := by
    rw [← inner_conj_symm, ← inner_conj_symm (countingDelta x) f, hright]
  have he := hleft.symm.trans (hd.trans hr)
  rw [← inner_conj_symm h (countingDelta y), countingDelta_inner, countingDelta_inner] at he
  exact he.symm

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- Reflecting the law transposes the Green kernel with the same killing set. -/
theorem reflected_killedGreen (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (x y : Γ) :
    killedGreen (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) A x y = killedGreen s μ A y x := by
  let sr := s.map ⟨Inv.inv, inv_injective⟩
  let μr := fun g => μ g⁻¹
  have hμr := reflected_jump_nonneg s μ hμ
  have hgapr := reflectedMarkov_spectral_gap s μ hgap
  let f := killedGreenColumn s μ hμ hgap A x
  let h := killedGreenColumn sr μr hμr hgapr A y
  have he := killed_columns_duality (rightMarkov s μ) A f h y x
    (fun z hz => killedGreenColumn_boundary s μ hμ hgap A x hz)
    (fun z hz => killedGreenColumn_boundary sr μr hμr hgapr A y hz)
    (fun z hz => killedGreenColumn_defect s μ hμ hgap A x hz)
    (fun z hz => by
      rw [rightMarkov_adjoint_eq_reflected]
      exact killedGreenColumn_defect sr μr hμr hgapr A y hz)
  change (killedGreenColumn s μ hμ hgap A x) y =
    (starRingEnd ℂ) ((killedGreenColumn sr μr hμr hgapr A y) x) at he
  rw [killedGreenColumn_apply, killedGreenColumn_apply, Complex.conj_ofReal] at he
  exact (Complex.ofReal_injective he).symm

end Singularity
