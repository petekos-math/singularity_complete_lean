import Singularity.FiniteEntranceDecomposition
import Singularity.GreenFirstHit

/-!
# Green comparison through a finite entrance set

The lower product inequality follows by stopping at one vertex. For an upper
comparison, stop on a finite set where Green rows are uniformly comparable to
the row at its center. The exact remainder is the killed Green kernel.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- The Green kernel satisfies the lower multiplicative comparison through
any intermediate vertex, with the diagonal Green normalizer. -/
theorem walkGreen_product_le (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x u y : Γ) :
    walkGreen s μ x u * walkGreen s μ u y ≤ walkGreen s μ u u * walkGreen s μ x y := by
  apply walkGreen_superharmonic_bound s μ hμ hmass hgap (fun z => walkGreen s μ z y)
    (fun z => walkGreen_nonneg s μ hμ z y) _ x u
  intro z
  have h := walkGreen_first_step s μ hgap z y
  have hδ : 0 ≤ (if z = y then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  linarith

/-- Local row comparison on a finite entrance set bounds its contribution
by the product through the chosen center. -/
theorem walkGreen_le_killed_add_product (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Finset Γ) (x u y : Γ) (C : ℝ) (hC : 0 ≤ C)
    (hfrom : ∀ a : A, walkGreen s μ a y ≤ C * walkGreen s μ u y)
    (hto : ∀ a : A, 1 ≤ C * walkGreen s μ a u) :
    walkGreen s μ x y ≤ killedGreen s μ (A : Set Γ) x y +
      C ^ 2 * walkGreen s μ x u * walkGreen s μ u y := by
  rw [walkGreen_finite_entrance_decomposition s μ hμ hmass hgap A x y]
  apply add_le_add le_rfl
  calc
    _ ≤ (C ^ 2 * walkGreen s μ u y) *
        (∑ a : A, firstEntranceKernel s μ (A : Set Γ) x a * walkGreen s μ a u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      have hF := firstEntranceKernel_nonneg s μ hμ (A : Set Γ) x a
      have hG := walkGreen_nonneg s μ hμ u y
      have hl : C * walkGreen s μ u y ≤
          (C * walkGreen s μ a u) * (C * walkGreen s μ u y) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hto a) (mul_nonneg hC hG)
      have hh := mul_le_mul_of_nonneg_left ((hfrom a).trans hl) hF
      convert hh using 1
      ring
    _ ≤ (C ^ 2 * walkGreen s μ u y) * walkGreen s μ x u :=
      mul_le_mul_of_nonneg_left (finite_entrance_green_sum_le s μ hμ hmass hgap A x u)
        (mul_nonneg (sq_nonneg _) (walkGreen_nonneg s μ hμ u y))
    _ = _ := by ring

end Singularity
