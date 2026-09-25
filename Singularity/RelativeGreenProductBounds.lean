import Singularity.RelativePairTransfer

/-!
# Product comparison through an additional finite stopping set

Inside a fixed killed domain, first entrance into B gives a product estimate
through a chosen center, with G_(A∪B) as the exact additive remainder.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- Relative Harnack bounds on a finite stopping set control the retained mass
without any cardinality factor. All Green values retain the original killing. -/
theorem killedGreen_le_union_add_product (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (B : Finset Γ) (x u y : Γ) (C : ℝ) (hC : 0 ≤ C)
    (hfrom : ∀ b : B, killedGreen s μ A b y ≤ C * killedGreen s μ A u y)
    (hto : ∀ b : B, 1 ≤ C * killedGreen s μ A b u) :
    killedGreen s μ A x y ≤ killedGreen s μ (A ∪ (B : Set Γ)) x y +
      C^2 * killedGreen s μ A x u * killedGreen s μ A u y := by
  have he := killedGreen_finite_entrance_decomposition s μ hμ hmass hgap A B x y
  rw [← Finset.sum_coe_sort B] at he
  rw [he]
  apply add_le_add le_rfl
  calc
    _ ≤ (C^2 * killedGreen s μ A u y) *
        (∑ b : B, firstEntranceKernel s μ (A ∪ (B : Set Γ)) x b * killedGreen s μ A b u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b _
      have hF := firstEntranceKernel_nonneg s μ hμ (A ∪ (B : Set Γ)) x b
      have hG := killedGreen_nonneg s μ hμ A u y
      have hl : C * killedGreen s μ A u y ≤
          (C * killedGreen s μ A b u) * (C * killedGreen s μ A u y) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hto b) (mul_nonneg hC hG)
      have hh := mul_le_mul_of_nonneg_left ((hfrom b).trans hl) hF
      convert hh using 1
      ring
    _ ≤ (C^2 * killedGreen s μ A u y) * killedGreen s μ A x u :=
      mul_le_mul_of_nonneg_left (relative_finite_entrance_sum_le s μ hμ hmass hgap A B x u)
        (mul_nonneg (sq_nonneg _) (killedGreen_nonneg s μ hμ A u y))
    _ = _ := by ring

end Singularity
