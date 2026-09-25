import Singularity.FirstEntranceColumn
import Singularity.HarmonicUniqueness

/-!
# The bounded first-entrance operator and the compressed Green renewal identity

The concrete supported Hilbert space models ℓ²(A). We construct F = G i G_A⁻¹
and prove, by uniqueness of the ℓ² Dirichlet problem, that its columns are exactly
the first-entrance path sums. Thus boundedness and the renewal identity are proved
for the probabilistic kernel, not assumed as block equations.
-/

noncomputable section
open MeasureTheory

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ]

variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ)

/-- The actual compressed Green operator, with its proved bounded inverse. -/
def walkGreenCompression : supportedL2 A ≃L[ℂ] supportedL2 A :=
  compressedGreenEquiv (rightMarkov s μ) (supportedInclusion A)
    (rightMarkov_contraction s μ hμ hmass) hgap

/-- Its action is the concrete compression of the resolvent. -/
theorem walkGreenCompression_apply (u : supportedL2 A) :
    walkGreenCompression s μ hμ hmass hgap A u =
      supportedRestriction A (green (rightMarkov s μ) (u : GroupL2 Γ)) := rfl

/-- The inverse of the concrete compression has norm at most two. -/
theorem walkGreenCompression_inverse_norm :
    ‖(walkGreenCompression s μ hμ hmass hgap A).symm.toContinuousLinearMap‖ ≤ 2 :=
  compressedGreen_inverse_norm (rightMarkov s μ) (supportedInclusion A)
    (rightMarkov_contraction s μ hμ hmass) hgap

/-- The bounded candidate for the first-entrance operator; its kernel is identified below. -/
def entranceOperator : supportedL2 A →L[ℂ] GroupL2 Γ :=
  (green (rightMarkov s μ)).comp ((supportedInclusion A).toContinuousLinearMap.comp
    (walkGreenCompression s μ hμ hmass hgap A).symm.toContinuousLinearMap)

/-- The operator takes the prescribed boundary values. -/
theorem entranceOperator_boundary (u : supportedL2 A) :
    supportedRestriction A (entranceOperator s μ hμ hmass hgap A u) = u := by
  change walkGreenCompression s μ hμ hmass hgap A
    ((walkGreenCompression s μ hμ hmass hgap A).symm u) = u
  exact ContinuousLinearEquiv.apply_symm_apply _ u

/-- Its values are P-harmonic outside A. -/
theorem entranceOperator_harmonic (u : supportedL2 A) {x : Γ} (hx : x ∉ A) :
    rightMarkov s μ (entranceOperator s μ hμ hmass hgap A u) x =
      entranceOperator s μ hμ hmass hgap A u x := by
  let v := (walkGreenCompression s μ hμ hmass hgap A).symm u
  have h := congrArg (countingEvaluation x)
    (green_right_inverse (rightMarkov s μ) hgap (v : GroupL2 Γ))
  rw [map_sub] at h
  simp only [countingEvaluation_apply] at h
  rw [v.property x hx] at h
  exact (sub_eq_zero.mp h).symm

/-- Its quantitative bound is inherited from G and the compressed inverse. -/
theorem entranceOperator_norm_le :
    ‖entranceOperator s μ hμ hmass hgap A‖ ≤ 2 * ‖green (rightMarkov s μ)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  let M := (walkGreenCompression s μ hμ hmass hgap A).symm.toContinuousLinearMap
  have hM : ‖M u‖ ≤ 2 * ‖u‖ := (M.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (walkGreenCompression_inverse_norm s μ hμ hmass hgap A)
      (norm_nonneg u))
  change ‖green (rightMarkov s μ) ((supportedInclusion A) (M u))‖ ≤ _
  calc
    _ ≤ ‖green (rightMarkov s μ)‖ * ‖supportedInclusion A (M u)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖green (rightMarkov s μ)‖ * ‖M u‖ := by rw [(supportedInclusion A).norm_map]
    _ ≤ ‖green (rightMarkov s μ)‖ * (2 * ‖u‖) :=
      mul_le_mul_of_nonneg_left hM (norm_nonneg _)
    _ = (2 * ‖green (rightMarkov s μ)‖) * ‖u‖ := by ring

variable [Countable Γ]

/-- Uniqueness identifies the operator columns with the first-entrance path columns. -/
theorem entranceOperator_delta (a : A) :
    entranceOperator s μ hμ hmass hgap A (supportedDelta A a) =
      firstEntranceColumn s μ hμ hgap A (a : Γ) := by
  apply harmonic_eq_of_boundary_eq (rightMarkov s μ)
    (rightMarkov_contraction s μ hμ hmass) hgap A
  · intro x hx
    rw [firstEntranceColumn_boundary s μ hμ hgap A (a : Γ) hx]
    have h := supportedRestriction_apply A
      (entranceOperator s μ hμ hmass hgap A (supportedDelta A a)) ⟨x, hx⟩
    rw [entranceOperator_boundary] at h
    exact h.symm
  · intro x hx
    exact entranceOperator_harmonic s μ hμ hmass hgap A _ hx
  · intro x hx
    exact firstEntranceColumn_harmonic s μ hμ hgap A (a : Γ) hx

/-- The matrix entries of the bounded operator are exactly F(x,a). -/
theorem entranceOperator_coefficient (a : A) (x : Γ) :
    entranceOperator s μ hμ hmass hgap A (supportedDelta A a) x =
      (firstEntranceKernel s μ A x a : ℂ) := by
  rw [entranceOperator_delta, firstEntranceColumn_apply]

omit [Countable Γ] in
/-- The concrete renewal identity G(·,A) = F G_A. -/
theorem entranceOperator_renewal :
    (entranceOperator s μ hμ hmass hgap A).comp
      (walkGreenCompression s μ hμ hmass hgap A).toContinuousLinearMap =
      (green (rightMarkov s μ)).comp (supportedInclusion A).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  change green (rightMarkov s μ) ((supportedInclusion A)
    ((walkGreenCompression s μ hμ hmass hgap A).symm
      (walkGreenCompression s μ hμ hmass hgap A u))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

end Singularity
