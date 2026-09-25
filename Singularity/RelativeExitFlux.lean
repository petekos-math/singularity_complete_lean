import Singularity.EntranceFinalJump

/-!
# Boundary flux after the last visit to an additional stopping set

Combining the final-jump formula with relative last entrance yields an exact
factorization of the first-entrance kernel. The inner infinite sums are proved
summable before they are interchanged with the finite jump sum.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The reflected entrance coefficient followed by the original final jump. -/
def boundaryExitFlux (s : Finset Γ) (μ : Γ → ℝ) (D : Set Γ) (a b : Γ) : ℝ :=
  ∑ g ∈ s, μ g * firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩)
    (fun g => μ g⁻¹) D (a * g⁻¹) b

theorem boundaryExitFlux_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (D : Set Γ) (a b : Γ) :
    0 ≤ boundaryExitFlux s μ D a b := by
  apply Finset.sum_nonneg
  intro g hg
  exact mul_nonneg (hμ g hg)
    (firstEntranceKernel_nonneg _ _ (reflected_jump_nonneg s μ hμ) D _ b)

theorem boundaryExitFlux_eq_zero_of_notMem (s : Finset Γ) (μ : Γ → ℝ)
    (D : Set Γ) (a b : Γ) (hb : b ∉ D) : boundaryExitFlux s μ D a b = 0 := by
  simp only [boundaryExitFlux, firstEntranceKernel_eq_zero_of_notMem _ _ D _ b hb,
    mul_zero, Finset.sum_const_zero]

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (A B : Set Γ)

include hμ hmass hgap in
/-- The factorization's finite jump sum can be interchanged with its infinite
last-entrance sum. -/
theorem relativeExitFlux_sum_exchange (x a : Γ) :
    (∑' b : Γ, killedGreen s μ A x b * boundaryExitFlux s μ (A ∪ B) a b) =
      ∑ g ∈ s, μ g * ∑' b : Γ, killedGreen s μ A x b *
        firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
          (A ∪ B) (a * g⁻¹) b := by
  have hs (g : Γ) (_hg : g ∈ s) :=
    (relativeGreen_last_entrance_summable s μ hμ hmass hgap A B x (a * g⁻¹)).mul_left (μ g)
  simp_rw [boundaryExitFlux, Finset.mul_sum, mul_left_comm (killedGreen s μ A x _)]
  rw [Summable.tsum_finsetSum hs]
  simp_rw [tsum_mul_left]

include hμ hmass hgap in
/-- Absolute convergence of the actual last-exit boundary factorization. -/
theorem relativeExitFlux_summable (x a : Γ) :
    Summable (fun b : Γ => killedGreen s μ A x b * boundaryExitFlux s μ (A ∪ B) a b) := by
  have hs (g : Γ) (_hg : g ∈ s) :=
    (relativeGreen_last_entrance_summable s μ hμ hmass hgap A B x (a * g⁻¹)).mul_left (μ g)
  have hh := (hasSum_sum (fun g hg => (hs g hg).hasSum)).summable
  simpa only [boundaryExitFlux, Finset.mul_sum, mul_left_comm] using hh

include hμ hmass hgap in
/-- The direct first entrance plus all last visits to the additional stopping
set account for the full first-entrance probability. -/
theorem firstEntranceKernel_relative_last_exit {a : Γ} (ha : a ∈ A) (x : Γ) :
    firstEntranceKernel s μ A x a = firstEntranceKernel s μ (A ∪ B) x a +
      ∑' b : Γ, killedGreen s μ A x b * boundaryExitFlux s μ (A ∪ B) a b := by
  rw [firstEntranceKernel_final_jump s μ hμ hmass hgap A ha,
    firstEntranceKernel_final_jump s μ hμ hmass hgap (A ∪ B) (Set.mem_union_left B ha),
    relativeExitFlux_sum_exchange s μ hμ hmass hgap A B]
  conv_lhs =>
    arg 2
    arg 2
    ext g
    rw [killedGreen_last_entrance_decomposition s μ hμ hmass hgap A B x (a * g⁻¹), mul_add]
  rw [Finset.sum_add_distrib, add_assoc]

end Singularity
