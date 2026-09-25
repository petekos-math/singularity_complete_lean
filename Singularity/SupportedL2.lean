import Singularity.CountingL2
import Singularity.Operators

/-!
# The closed Hilbert subspace supported on a subset

We model ℓ²(A) as the closed subspace of counting-measure L²(X) consisting
of functions zero outside A. Its inclusion is the extension-by-zero map.
The adjoint of this inclusion is proved to retain exactly the coordinates in A.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace Singularity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Subtraction of counting-measure L² vectors is pointwise. -/
theorem counting_sub_apply (f g : GroupL2 X) (x : X) : (f - g) x = f x - g x := by
  simpa only [countingEvaluation_apply] using (countingEvaluation x).map_sub f g

/-- Addition of counting-measure L² vectors is pointwise. -/
theorem counting_add_apply (f g : GroupL2 X) (x : X) : (f + g) x = f x + g x := by
  simpa only [countingEvaluation_apply] using (countingEvaluation x).map_add f g

/-- Scalar multiplication of counting-measure L² vectors is pointwise. -/
theorem counting_smul_apply (c : ℂ) (f : GroupL2 X) (x : X) : (c • f) x = c * f x := by
  simpa only [countingEvaluation_apply, smul_eq_mul] using (countingEvaluation x).map_smul c f

/-- The concrete supported subspace, with its inherited Hilbert norm. -/
def supportedL2 (A : Set X) : Submodule ℂ (GroupL2 X) where
  carrier := {f | ∀ x, x ∉ A → f x = 0}
  zero_mem' := by intro x _; exact Measure.ae_count_iff.mp (Lp.coeFn_zero _ _ _) x
  add_mem' := by
    intro f g hf hg x hx
    rw [counting_add_apply, hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro c f hf x hx
    rw [counting_smul_apply, hf x hx, mul_zero]

/-- Point evaluations are continuous, so the supported subspace is closed. -/
theorem supportedL2_closed (A : Set X) : IsClosed (supportedL2 A : Set (GroupL2 X)) := by
  have he : (supportedL2 A : Set (GroupL2 X)) =
      ⋂ x : X, ⋂ (_ : x ∉ A), {f : GroupL2 X | countingEvaluation x f = 0} := by
    ext f
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, countingEvaluation_apply]
    rfl
  rw [he]
  exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
    isClosed_eq (countingEvaluation x).continuous continuous_const))

instance supportedL2_completeSpace (A : Set X) : CompleteSpace (supportedL2 A) :=
  (supportedL2_closed A).completeSpace_coe

/-- Extension by zero, realized as the isometric inclusion of the supported subspace. -/
def supportedInclusion (A : Set X) : supportedL2 A →ₗᵢ[ℂ] GroupL2 X :=
  (supportedL2 A).subtypeₗᵢ

/-- A singleton in A is a vector of the supported Hilbert space. -/
def supportedDelta (A : Set X) (a : A) : supportedL2 A :=
  ⟨countingDelta a, by
    intro x hx
    rw [countingDelta_apply]
    split_ifs with h
    · exact (hx (h ▸ a.property)).elim
    · rfl⟩

/-- Restriction from the full Hilbert space to the supported Hilbert space. -/
def supportedRestriction (A : Set X) : GroupL2 X →L[ℂ] supportedL2 A :=
  (supportedInclusion A).toContinuousLinearMap.adjoint

/-- Restriction keeps every coordinate in A. -/
theorem supportedRestriction_apply (A : Set X) (f : GroupL2 X) (a : A) :
    ((supportedRestriction A f : supportedL2 A) : GroupL2 X) a = f a := by
  have h := (supportedInclusion A).toContinuousLinearMap.adjoint_inner_right
    (supportedDelta A a) f
  change inner ℂ (supportedDelta A a) (supportedRestriction A f) =
    inner ℂ (countingDelta (a : X)) f at h
  change inner ℂ (countingDelta (a : X)) ((supportedRestriction A f : supportedL2 A) : GroupL2 X) =
    inner ℂ (countingDelta (a : X)) f at h
  simpa only [countingDelta_inner] using h

/-- The restriction of an included vector is that vector. -/
theorem supportedRestriction_inclusion (A : Set X) (f : supportedL2 A) :
    supportedRestriction A (supportedInclusion A f) = f := by
  apply Subtype.ext
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro x
  by_cases hx : x ∈ A
  · exact supportedRestriction_apply A (f : GroupL2 X) ⟨x, hx⟩
  · rw [(supportedRestriction A (supportedInclusion A f)).property x hx, f.property x hx]

/-- The compressed operator retains exactly the A-coordinates of T on supported inputs. -/
theorem supported_compression_apply (A : Set X) (T : GroupL2 X →L[ℂ] GroupL2 X)
    (f : supportedL2 A) (a : A) :
    ((compression (supportedInclusion A) T f : supportedL2 A) : GroupL2 X) a =
      T (f : GroupL2 X) a :=
  supportedRestriction_apply A (T (f : GroupL2 X)) a

end Singularity
