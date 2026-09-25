import Singularity.RelativeLastEntrance

/-!
# First- and last-entrance transfers inside a fixed killed domain

The additional finite stopping set changes one endpoint, while the original
killing set is retained in every entrance coefficient and Green value.
Reflection identifies both discarded parts with the same union-killed kernel.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Actual endpoint transfer before hitting the original killing set A. -/
def relativePairTransfer (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (B : Finset Γ) (last : Bool) :
    (Γ × Γ → ℝ) →ₗ[ℝ] (Γ × Γ → ℝ) where
  toFun f p := ∑ b : B,
    (if last then firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A ∪ (B : Set Γ)) p.2 b
      else firstEntranceKernel s μ (A ∪ (B : Set Γ)) p.1 b) *
      f (if last then (p.1, (b : Γ)) else ((b : Γ), p.2))
  map_add' f g := by ext p; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext p; simp [Finset.mul_sum, mul_left_comm]

/-- Positivity preserves comparisons on the admissible successor pairs. -/
theorem relativePairTransfer_monoOn (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (A : Set Γ) (B : Finset Γ) (last : Bool) (S S' : Set (Γ × Γ))
    (hmove : ∀ p ∈ S, ∀ b : B, (if last then (p.1, (b : Γ)) else ((b : Γ), p.2)) ∈ S')
    (f g : Γ × Γ → ℝ) (hfg : ∀ p ∈ S', f p ≤ g p) :
    ∀ p ∈ S, relativePairTransfer s μ A B last f p ≤ relativePairTransfer s μ A B last g p := by
  intro p hp
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left (hfg _ (hmove p hp b))
  cases last
  · exact firstEntranceKernel_nonneg s μ hμ _ p.1 b
  · exact firstEntranceKernel_nonneg _ _ (reflected_jump_nonneg s μ hμ) _ p.2 b

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]

/-- The finite relative first-entrance contribution is bounded by G_A. -/
theorem relative_finite_entrance_sum_le (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (B : Finset Γ) (x y : Γ) :
    (∑ b : B, firstEntranceKernel s μ (A ∪ (B : Set Γ)) x b * killedGreen s μ A b y) ≤
      killedGreen s μ A x y := by
  have hh := killedGreen_finite_entrance_decomposition s μ hμ hmass hgap A B x y
  rw [← Finset.sum_coe_sort B] at hh
  linarith [killedGreen_nonneg s μ hμ (A ∪ (B : Set Γ)) x y]

/-- The reflected finite last-entrance contribution is also bounded by G_A. -/
theorem relative_finite_last_entrance_sum_le (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (B : Finset Γ) (x y : Γ) :
    (∑ b : B, firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
      (A ∪ (B : Set Γ)) y b * killedGreen s μ A x b) ≤ killedGreen s μ A x y := by
  have hh := killedGreen_finite_last_entrance_decomposition s μ hμ hmass hgap A B x y
  rw [← Finset.sum_coe_sort B] at hh
  simp only [mul_comm (killedGreen s μ A x _)] at hh
  linarith [killedGreen_nonneg s μ hμ (A ∪ (B : Set Γ)) x y]

/-- In either orientation, the discarded part is precisely G_(A∪B). -/
theorem relativePairTransfer_green_decomposition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (B : Finset Γ)
    (last : Bool) (p : Γ × Γ) :
    killedGreen s μ A p.1 p.2 = killedGreen s μ (A ∪ (B : Set Γ)) p.1 p.2 +
      relativePairTransfer s μ A B last (fun q => killedGreen s μ A q.1 q.2) p := by
  cases last
  · change killedGreen s μ A p.1 p.2 = _ +
      ∑ b : B, firstEntranceKernel s μ (A ∪ (B : Set Γ)) p.1 b * killedGreen s μ A b p.2
    have hh := killedGreen_finite_entrance_decomposition s μ hμ hmass hgap A B p.1 p.2
    rw [← Finset.sum_coe_sort B] at hh
    exact hh
  · change killedGreen s μ A p.1 p.2 = _ +
      ∑ b : B, firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
        (A ∪ (B : Set Γ)) p.2 b * killedGreen s μ A p.1 b
    have hh := killedGreen_finite_last_entrance_decomposition s μ hμ hmass hgap A B p.1 p.2
    rw [← Finset.sum_coe_sort B] at hh
    simpa only [mul_comm] using hh

/-- Every transfer decreases the relative product through a fixed vertex. -/
theorem relativePairTransfer_product_le (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (B : Finset Γ)
    (last : Bool) (o : Γ) (p : Γ × Γ) :
    relativePairTransfer s μ A B last (fun q => killedGreen s μ A q.1 o * killedGreen s μ A o q.2) p ≤
      killedGreen s μ A p.1 o * killedGreen s μ A o p.2 := by
  cases last
  · change (∑ b : B, firstEntranceKernel s μ (A ∪ (B : Set Γ)) p.1 b *
      (killedGreen s μ A b o * killedGreen s μ A o p.2)) ≤ _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (relative_finite_entrance_sum_le s μ hμ hmass hgap A B p.1 o)
      (killedGreen_nonneg s μ hμ A o p.2)
  · change (∑ b : B, firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
      (A ∪ (B : Set Γ)) p.2 b * (killedGreen s μ A p.1 o * killedGreen s μ A o b)) ≤ _
    simp_rw [mul_left_comm _ (killedGreen s μ A p.1 o)]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (relative_finite_last_entrance_sum_le s μ hμ hmass hgap A B o p.2)
      (killedGreen_nonneg s μ hμ A p.1 o)

end Singularity
