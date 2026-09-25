import Singularity.GreenPositive
import Singularity.GreenAdjoint

/-!
# Semigroup generation and reflection of the finite support

The reflected walk inherits positivity, normalization, and semigroup generation.
Finite generation also supplies countability of the group via its finite words.
-/

noncomputable section

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Reflection carries a positive finite jump law to a positive finite jump law. -/
theorem reflected_jump_pos (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g) :
    ∀ g ∈ s.map ⟨Inv.inv, inv_injective⟩, 0 < μ g⁻¹ := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
  simpa only [Function.Embedding.coeFn_mk, inv_inv] using hpos a ha

/-- Reflection preserves total jump mass. -/
theorem reflected_jump_mass (s : Finset Γ) (μ : Γ → ℝ) :
    ∑ g ∈ s.map ⟨Inv.inv, inv_injective⟩, μ g⁻¹ = ∑ g ∈ s, μ g := by
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, inv_inv]

/-- Reflecting a semigroup-generating support still generates as a semigroup. -/
theorem reflected_support_generates (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    Submonoid.closure (s.map ⟨Inv.inv, inv_injective⟩ : Set Γ) = ⊤ := by
  have hinv : ∀ g ∈ Submonoid.closure (s : Set Γ),
      g⁻¹ ∈ Submonoid.closure (s.map ⟨Inv.inv, inv_injective⟩ : Set Γ) := by
    intro g hg
    induction hg using Submonoid.closure_induction_left with
    | one => simpa only [inv_one] using Submonoid.one_mem _
    | mul_left a ha b _ ih =>
      rw [mul_inv_rev]
      apply Submonoid.mul_mem _ ih
      exact Submonoid.subset_closure (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
  apply top_unique
  intro g _
  have hg : g⁻¹ ∈ Submonoid.closure (s : Set Γ) := by rw [hgen]; trivial
  simpa only [inv_inv] using hinv g⁻¹ hg

/-- Finite semigroup generation implies countability via the finite jump words. -/
theorem countable_of_finite_jump_generation (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) : Countable Γ := by
  let f : (Σ n : ℕ, WalkWord s n) → Γ := fun p => walkEndpoint s p.1 1 p.2
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨n, w, hw⟩ := exists_walkWord_between s hgen 1 g
    exact ⟨⟨n, w⟩, hw⟩
  exact hf.countable

end Singularity
