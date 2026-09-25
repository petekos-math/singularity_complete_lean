import Singularity.FiniteEntranceDecomposition
import Singularity.ReflectedSupport

/-!
# The finite last-entry decomposition through the reflected walk

The first-entry formula for the reflected law transposes into a last-entry
formula for the original Green kernel. No symmetry of the measure is assumed.
The remainder is explicitly the reflected killed kernel with reversed endpoints.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ] in
/-- Reflection preserves nonnegativity, also for zero-weight support entries. -/
theorem reflected_jump_nonneg (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g) :
    ∀ g ∈ s.map ⟨Inv.inv, inv_injective⟩, 0 ≤ μ g⁻¹ := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
  simpa only [Function.Embedding.coeFn_mk, inv_inv] using hμ a ha

/-- The reflected first-entry identity is the last-entry identity for G. -/
theorem walkGreen_finite_last_entrance_decomposition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x y : Γ) :
    walkGreen s μ x y =
      killedGreen (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A : Set Γ) y x +
      ∑ a : A, firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
        (A : Set Γ) y a * walkGreen s μ x a := by
  have h := walkGreen_finite_entrance_decomposition
    (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (reflected_jump_nonneg s μ hμ)
    ((reflected_jump_mass s μ).trans hmass) (reflectedMarkov_spectral_gap s μ hgap) A y x
  simpa only [reflected_walkGreen s μ hgap] using h

/-- The last-entry sum is bounded by the original Green kernel. -/
theorem finite_last_entrance_green_sum_le (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x y : Γ) :
    (∑ a : A, firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
      (A : Set Γ) y a * walkGreen s μ x a) ≤ walkGreen s μ x y := by
  have h := finite_entrance_green_sum_le (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflected_jump_nonneg s μ hμ) ((reflected_jump_mass s μ).trans hmass)
    (reflectedMarkov_spectral_gap s μ hgap) A y x
  simpa only [reflected_walkGreen s μ hgap] using h

end Singularity
