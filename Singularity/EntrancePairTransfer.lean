import Singularity.FiniteLastEntrance

/-!
# First- and last-entry transfers on endpoint pairs

Each transfer replaces one endpoint by a first-entry location in a finite set.
Updating the right endpoint uses the reflected law, so symmetry is not needed.
These actual path-kernel transfers preserve local inequalities, decompose G,
and decrease the product potential G(x,o)G(o,y).
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- A first-entry step if `last=false`, a reflected last-entry step if `last=true`. -/
def entrancePairTransfer (s : Finset Γ) (μ : Γ → ℝ) (A : Finset Γ) (last : Bool) :
    (Γ × Γ → ℝ) →ₗ[ℝ] (Γ × Γ → ℝ) where
  toFun f p := ∑ a : A,
    (if last then firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A : Set Γ) p.2 a
      else firstEntranceKernel s μ (A : Set Γ) p.1 a) *
      f (if last then (p.1, (a : Γ)) else ((a : Γ), p.2))
  map_add' f g := by ext p; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext p; simp [Finset.mul_sum, mul_left_comm]

/-- The discarded contribution, keeping the orientation of the walk explicit. -/
def entrancePairRemainder (s : Finset Γ) (μ : Γ → ℝ) (A : Finset Γ) (last : Bool)
    (p : Γ × Γ) : ℝ :=
  if last then killedGreen (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A : Set Γ) p.2 p.1
  else killedGreen s μ (A : Set Γ) p.1 p.2

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ] in
/-- A transfer preserves an inequality known only on all its successor pairs. -/
theorem entrancePairTransfer_monoOn (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (A : Finset Γ) (last : Bool) (S S' : Set (Γ × Γ))
    (hmove : ∀ p ∈ S, ∀ a : A, (if last then (p.1, (a : Γ)) else ((a : Γ), p.2)) ∈ S')
    (f g : Γ × Γ → ℝ) (hfg : ∀ p ∈ S', f p ≤ g p) :
    ∀ p ∈ S, entrancePairTransfer s μ A last f p ≤ entrancePairTransfer s μ A last g p := by
  intro p hp
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left (hfg _ (hmove p hp a))
  cases last
  · exact firstEntranceKernel_nonneg s μ hμ (A : Set Γ) p.1 a
  · exact firstEntranceKernel_nonneg _ _ (reflected_jump_nonneg s μ hμ) (A : Set Γ) p.2 a

/-- The Green kernel is exactly the retained part plus the discarded part. -/
theorem entrancePairTransfer_green_decomposition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (last : Bool) (p : Γ × Γ) :
    walkGreen s μ p.1 p.2 = entrancePairRemainder s μ A last p +
      entrancePairTransfer s μ A last (fun q => walkGreen s μ q.1 q.2) p := by
  cases last
  · exact walkGreen_finite_entrance_decomposition s μ hμ hmass hgap A p.1 p.2
  · exact walkGreen_finite_last_entrance_decomposition s μ hμ hmass hgap A p.1 p.2

/-- Either orientation decreases the product of Green kernels through o. -/
theorem entrancePairTransfer_product_le (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (last : Bool)
    (o : Γ) (p : Γ × Γ) :
    entrancePairTransfer s μ A last (fun q => walkGreen s μ q.1 o * walkGreen s μ o q.2) p ≤
      walkGreen s μ p.1 o * walkGreen s μ o p.2 := by
  cases last
  · change (∑ a : A, firstEntranceKernel s μ (A : Set Γ) p.1 a *
      (walkGreen s μ a o * walkGreen s μ o p.2)) ≤ _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (finite_entrance_green_sum_le s μ hμ hmass hgap A p.1 o)
      (walkGreen_nonneg s μ hμ o p.2)
  · change (∑ a : A, firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
      (A : Set Γ) p.2 a * (walkGreen s μ p.1 o * walkGreen s μ o a)) ≤ _
    simp_rw [mul_left_comm _ (walkGreen s μ p.1 o)]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (finite_last_entrance_green_sum_le s μ hμ hmass hgap A o p.2)
      (walkGreen_nonneg s μ hμ p.1 o)

end Singularity
