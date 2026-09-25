import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Semigroup generation through an involutive kernel

If a surjective group homomorphism has kernel elements of square one, the
full inverse image of a nonempty semigroup-generating set also generates.
This justifies lifting every projective jump with both central signs; it does
not replace semigroup generation by group generation.
-/

noncomputable section
open Set

namespace Singularity

/-- Lifts of a semigroup-generating set map onto the whole target group. -/
theorem closure_preimage_maps_onto {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Surjective φ) (s : Set H)
    (hs : Submonoid.closure s = ⊤) :
    ∀ h : H, ∃ g ∈ Submonoid.closure (φ ⁻¹' s), φ g = h := by
  intro h
  have hh : h ∈ Submonoid.closure s := hs ▸ Submonoid.mem_top h
  induction hh using Submonoid.closure_induction with
  | mem h hh =>
    obtain ⟨g, rfl⟩ := hφ h
    exact ⟨g, Submonoid.subset_closure hh, rfl⟩
  | one => exact ⟨1, Submonoid.one_mem _, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨g, hg, he⟩ := ha
    obtain ⟨k, hk, hf⟩ := hb
    exact ⟨g * k, Submonoid.mul_mem _ hg hk, by rw [map_mul, he, hf]⟩

/-- Taking the whole inverse-image jump set preserves semigroup generation
when every kernel element is an involution. -/
theorem closure_preimage_eq_top_of_involutive_kernel {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Surjective φ) (s : Set H) (hne : s.Nonempty)
    (hs : Submonoid.closure s = ⊤) (hker : ∀ g, φ g = 1 → g ^ 2 = 1) :
    Submonoid.closure (φ ⁻¹' s) = ⊤ := by
  let T := Submonoid.closure (φ ⁻¹' s)
  have honto : ∀ h : H, ∃ g ∈ T, φ g = h := closure_preimage_maps_onto φ hφ s hs
  have hK : ∀ k, φ k = 1 → k ∈ T := by
    intro k hk
    obtain ⟨a₀, ha₀⟩ := hne
    obtain ⟨a, rfl⟩ := hφ a₀
    have ha : a ∈ T := Submonoid.subset_closure ha₀
    obtain ⟨b, hb, he⟩ := honto (φ a)⁻¹
    have hab : φ (a * b) = 1 := by rw [map_mul, he, mul_inv_cancel]
    have hab2 := hker (a * b) hab
    have hka : k * a ∈ T := Submonoid.subset_closure (by
      change φ (k * a) ∈ s
      simpa only [map_mul, hk, one_mul] using ha₀)
    have hm := T.mul_mem (T.mul_mem hka hb) (T.mul_mem ha hb)
    have heq : (k * a * b) * (a * b) = k := by
      calc
        _ = k * (a * b) ^ 2 := by simp only [pow_two, mul_assoc]
        _ = k := by rw [hab2, mul_one]
    rwa [heq] at hm
  apply top_unique
  intro g _
  obtain ⟨h, hh, he⟩ := honto (φ g)
  have hk : φ (g * h⁻¹) = 1 := by rw [map_mul, map_inv, he, mul_inv_cancel]
  have hm := T.mul_mem (hK _ hk) hh
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

end Singularity
