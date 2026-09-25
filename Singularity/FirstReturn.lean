import Singularity.EntranceOperator

/-!
# First positive return and the inverse compressed Green operator

The nth term here counts a return at time n+1: take the first jump, then first
enter A in n further jumps. The path series is summed with convergence proved.
Its operator is R_A = i* P F, and the renewal calculation proves G_A⁻¹ = I-R_A.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ]

/-- Weight of first return at time n+1, when the starting point is in A. -/
def firstReturnWeight (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (n : ℕ) (a b : Γ) : ℝ :=
  ∑ g ∈ s, μ g * firstEntranceWeight s μ A n (a * g) b

/-- The first-positive-return kernel as an actual path sum. -/
def firstReturnKernel (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (a b : Γ) : ℝ :=
  ∑' n : ℕ, firstReturnWeight s μ A n a b

variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ)

include hμ hgap

/-- The return series converges to its first-jump decomposition. -/
theorem firstReturn_hasSum (a b : Γ) :
    HasSum (fun n : ℕ => firstReturnWeight s μ A n a b)
      (∑ g ∈ s, μ g * firstEntranceKernel s μ A (a * g) b) := by
  apply hasSum_sum
  intro g _
  exact ((firstEntranceWeight_summable s μ hμ hgap A (a * g) b).hasSum).mul_left (μ g)

/-- The first-return kernel is the finite first-jump sum of entrance kernels. -/
theorem firstReturnKernel_eq (a b : Γ) :
    firstReturnKernel s μ A a b = ∑ g ∈ s, μ g * firstEntranceKernel s μ A (a * g) b :=
  (firstReturn_hasSum s μ hμ hgap A a b).tsum_eq

/-- First-return entries are nonnegative. -/
theorem firstReturnKernel_nonneg (a b : Γ) : 0 ≤ firstReturnKernel s μ A a b := by
  rw [firstReturnKernel_eq s μ hμ hgap]
  exact Finset.sum_nonneg (fun g hg =>
    mul_nonneg (hμ g hg) (firstEntranceKernel_nonneg s μ hμ A (a * g) b))

/-- The actual bounded return operator on the supported Hilbert space. -/
def firstReturnOperator : supportedL2 A →L[ℂ] supportedL2 A :=
  (supportedRestriction A).comp ((rightMarkov s μ).comp (entranceOperator s μ hμ hmass hgap A))

/-- The full-space defect of F is extension by zero of G_A⁻¹. -/
theorem entranceOperator_defect (u : supportedL2 A) :
    entranceOperator s μ hμ hmass hgap A u -
      rightMarkov s μ (entranceOperator s μ hμ hmass hgap A u) =
      supportedInclusion A ((walkGreenCompression s μ hμ hmass hgap A).symm u) :=
  green_right_inverse (rightMarkov s μ) hgap _

/-- Applying restriction to the defect gives the renewal identity on A. -/
theorem firstReturnOperator_defect (u : supportedL2 A) :
    u - firstReturnOperator s μ hμ hmass hgap A u =
      (walkGreenCompression s μ hμ hmass hgap A).symm u := by
  have h := congrArg (supportedRestriction A) (entranceOperator_defect s μ hμ hmass hgap A u)
  rw [map_sub, entranceOperator_boundary, supportedRestriction_inclusion] at h
  exact h

/-- The inverse compression is exactly I minus the first-positive-return operator. -/
theorem walkGreenCompression_inverse_eq_id_sub_return :
    (walkGreenCompression s μ hμ hmass hgap A).symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (supportedL2 A) - firstReturnOperator s μ hμ hmass hgap A := by
  apply ContinuousLinearMap.ext
  intro u
  exact (firstReturnOperator_defect s μ hμ hmass hgap A u).symm

variable [Countable Γ]

/-- The return operator has exactly the path-counting first-return coefficients. -/
theorem firstReturnOperator_coefficient (a b : A) :
    ((firstReturnOperator s μ hμ hmass hgap A (supportedDelta A b) : supportedL2 A) : GroupL2 Γ) a =
      (firstReturnKernel s μ A a b : ℂ) := by
  change ((supportedRestriction A (rightMarkov s μ
    (entranceOperator s μ hμ hmass hgap A (supportedDelta A b))) : supportedL2 A) : GroupL2 Γ) a = _
  rw [supportedRestriction_apply, rightMarkov_apply, firstReturnKernel_eq s μ hμ hgap]
  simp_rw [entranceOperator_coefficient]
  push_cast
  rfl

/-- Matrix entries of M_A: a diagonal identity term minus a nonnegative return kernel. -/
theorem walkGreenCompression_inverse_coefficient (a b : A) :
    (((walkGreenCompression s μ hμ hmass hgap A).symm (supportedDelta A b) : supportedL2 A) :
      GroupL2 Γ) a = (if (a : Γ) = (b : Γ) then 1 else 0) - (firstReturnKernel s μ A a b : ℂ) := by
  rw [← firstReturnOperator_defect s μ hμ hmass hgap A (supportedDelta A b)]
  change ((supportedDelta A b : GroupL2 Γ) -
    (firstReturnOperator s μ hμ hmass hgap A (supportedDelta A b) : GroupL2 Γ)) a = _
  rw [counting_sub_apply, firstReturnOperator_coefficient]
  exact congrArg (fun z : ℂ => z - (firstReturnKernel s μ A a b : ℂ))
    (countingDelta_apply (b : Γ) (a : Γ))

end Singularity
