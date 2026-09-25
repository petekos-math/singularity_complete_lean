import Singularity.SupportedL2
import Singularity.Green

/-!
# Uniqueness for the ℓ² Dirichlet problem

For a contraction P with I-P invertible, an ℓ² vector that vanishes on A and
is P-harmonic outside A must be zero. This does not require symmetry or a
spectral-gap theorem for the killed walk.
-/

noncomputable section
open MeasureTheory

namespace Singularity

/-- Orthogonality of the defect of a contraction forces the vector to be fixed. -/
theorem contraction_fixed_of_defect_inner_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : E →L[ℂ] E) (hP : ∀ v, ‖P v‖ ≤ ‖v‖) (v : E)
    (hinner : inner ℂ v (v - P v) = 0) : P v = v := by
  have hi := congrArg (fun z : ℂ => RCLike.re z) hinner
  simp only [inner_sub_right, map_sub, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, RCLike.ofReal_re, map_zero] at hi
  have hn := norm_sub_sq (𝕜 := ℂ) v (P v)
  have hb := pow_le_pow_left₀ (norm_nonneg (P v)) (hP v) 2
  have hz : ‖v - P v‖ = 0 := by nlinarith [norm_nonneg (v - P v)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The concrete counting-measure ℓ² Dirichlet problem has at most one solution. -/
theorem harmonic_zero_of_boundary_zero (P : GroupL2 X →L[ℂ] GroupL2 X)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) (hgap : spectralRadius ℂ P < 1)
    (A : Set X) (f : GroupL2 X) (hA : ∀ x ∈ A, f x = 0)
    (hharm : ∀ x, x ∉ A → P f x = f x) : f = 0 := by
  have hinner : inner ℂ f (f - P f) = 0 := by
    rw [L2.inner_def]
    have hz : (fun x => inner ℂ (f x) ((f - P f) x)) = fun _ => (0 : ℂ) := by
      funext x
      by_cases hx : x ∈ A
      · rw [hA x hx, inner_zero_left]
      · rw [counting_sub_apply, hharm x hx, sub_self, inner_zero_right]
    rw [hz, integral_zero]
  have hfixed := contraction_fixed_of_defect_inner_zero P hP f hinner
  have hi := green_left_inverse P hgap f
  rw [hfixed, sub_self, map_zero] at hi
  exact hi.symm

/-- Two ℓ² solutions with the same boundary values and exterior harmonicity coincide. -/
theorem harmonic_eq_of_boundary_eq (P : GroupL2 X →L[ℂ] GroupL2 X)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) (hgap : spectralRadius ℂ P < 1)
    (A : Set X) (f g : GroupL2 X) (hA : ∀ x ∈ A, f x = g x)
    (hf : ∀ x, x ∉ A → P f x = f x)
    (hg : ∀ x, x ∉ A → P g x = g x) : f = g := by
  apply sub_eq_zero.mp
  apply harmonic_zero_of_boundary_zero P hP hgap A (f - g)
  · intro x hx
    rw [counting_sub_apply, hA x hx, sub_self]
  · intro x hx
    rw [map_sub, counting_sub_apply, counting_sub_apply, hf x hx, hg x hx]

/-- The same uniqueness statement for equal inhomogeneous exterior defects. -/
theorem dirichlet_eq_of_defect_eq (P : GroupL2 X →L[ℂ] GroupL2 X)
    (hP : ∀ v, ‖P v‖ ≤ ‖v‖) (hgap : spectralRadius ℂ P < 1)
    (A : Set X) (f g : GroupL2 X) (hA : ∀ x ∈ A, f x = g x)
    (hd : ∀ x, x ∉ A → (f - P f) x = (g - P g) x) : f = g := by
  apply sub_eq_zero.mp
  apply harmonic_zero_of_boundary_zero P hP hgap A (f - g)
  · intro x hx
    rw [counting_sub_apply, hA x hx, sub_self]
  · intro x hx
    have h := hd x hx
    simp only [counting_sub_apply] at h
    rw [map_sub, counting_sub_apply, counting_sub_apply]
    linear_combination -h

end Singularity
