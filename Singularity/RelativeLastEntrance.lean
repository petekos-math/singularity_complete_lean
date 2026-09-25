import Singularity.KilledGreenReflection

/-!
# Last entrance inside killed domains

Reflection turns the proved relative first-entrance decomposition into the
last-entrance identity for the original walk. The last factor is the actual
first-entrance kernel of the reflected law, with both killing sets retained.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (A B : Set Γ)

include hμ hmass hgap in
/-- The last-entrance series inside A's surviving domain is absolutely convergent. -/
theorem relativeGreen_last_entrance_summable (x y : Γ) :
    Summable (fun b : Γ => killedGreen s μ A x b *
      firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A ∪ B) y b) := by
  have hh := relativeGreen_entrance_summable (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflected_jump_nonneg s μ hμ) (by simpa only [reflected_jump_mass] using hmass)
    (reflectedMarkov_spectral_gap s μ hgap) A B y x
  simpa only [reflected_killedGreen s μ hμ hgap, mul_comm] using hh

include hμ hmass hgap in
/-- Exact last-entrance identity, allowing infinite additional stopping sets. -/
theorem killedGreen_last_entrance_decomposition (x y : Γ) :
    killedGreen s μ A x y = killedGreen s μ (A ∪ B) x y +
      ∑' b : Γ, killedGreen s μ A x b *
        firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A ∪ B) y b := by
  have hh := killedGreen_entrance_decomposition (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflected_jump_nonneg s μ hμ) (by simpa only [reflected_jump_mass] using hmass)
    (reflectedMarkov_spectral_gap s μ hgap) A B y x
  simpa only [reflected_killedGreen s μ hμ hgap, mul_comm] using hh

include hμ hmass hgap in
/-- Finite additional stopping sets give finite last-entrance sums. -/
theorem killedGreen_finite_last_entrance_decomposition (B : Finset Γ) (x y : Γ) :
    killedGreen s μ A x y = killedGreen s μ (A ∪ (B : Set Γ)) x y +
      ∑ b ∈ B, killedGreen s μ A x b *
        firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A ∪ (B : Set Γ)) y b := by
  have hh := killedGreen_finite_entrance_decomposition (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflected_jump_nonneg s μ hμ) (by simpa only [reflected_jump_mass] using hmass)
    (reflectedMarkov_spectral_gap s μ hgap) A B y x
  simpa only [reflected_killedGreen s μ hμ hgap, mul_comm] using hh

include hμ hmass hgap in
/-- Last entrance can only decrease the Green mass inside the original domain. -/
theorem relativeGreen_last_entrance_sum_le (x y : Γ) :
    (∑' b : Γ, killedGreen s μ A x b *
      firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A ∪ B) y b) ≤ killedGreen s μ A x y := by
  rw [killedGreen_last_entrance_decomposition s μ hμ hmass hgap A B x y]
  exact le_add_of_nonneg_left (killedGreen_nonneg s μ hμ _ _ _)

end Singularity
