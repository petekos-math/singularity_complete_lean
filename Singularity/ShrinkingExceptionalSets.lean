import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Finite correction covers for shrinking exceptional sets

If the complements of a sequence of shadows shrink toward a closed set Z,
points outside Z eventually lie in every shadow. Compactness gives finitely
many corrections whenever no orbit is contained in Z. Finite Z and infinite
orbits are a sufficient special case.
-/

open Set Filter
open scoped Topology

namespace Singularity

/-- A point outside the exceptional set eventually belongs to the shadows. -/
theorem eventually_mem_of_shrinking_complements {B : Type*} [TopologicalSpace B] [T1Space B]
    (T : ℕ → Set B) (Z : Set B)
    (hshrink : ∀ U : Set B, IsOpen U → Z ⊆ U → ∀ᶠ n in atTop, (T n)ᶜ ⊆ U)
    {ξ : B} (hξ : ξ ∉ Z) : ∀ᶠ n in atTop, ξ ∈ T n := by
  have hsub : Z ⊆ ({ξ} : Set B)ᶜ := by
    intro η hη
    simp only [mem_compl_iff, mem_singleton_iff]
    intro he
    exact hξ (he ▸ hη)
  filter_upwards [hshrink {ξ}ᶜ isClosed_singleton.isOpen_compl hsub] with n hn
  by_contra hnot
  have h := hn hnot
  simp at h

/-- Compactness turns orbit escape from a closed exceptional set into a
finite corrected eventual cover of the entire space. -/
theorem finite_corrected_eventual_cover_of_shrinking_complements
    {Γ B : Type*} [Group Γ] [TopologicalSpace B] [CompactSpace B] [T1Space B]
    [MulAction Γ B] [ContinuousConstSMul Γ B]
    (T : ℕ → Set B) (Z : Set B) (hZ : IsClosed Z)
    (hescape : ∀ ξ : B, ∃ a : Γ, a⁻¹ • ξ ∉ Z)
    (hshrink : ∀ U : Set B, IsOpen U → Z ⊆ U → ∀ᶠ n in atTop, (T n)ᶜ ⊆ U) :
    ∃ F : Finset Γ, ∀ ξ : B, ∃ a ∈ F, ∀ᶠ n in atTop, a⁻¹ • ξ ∈ T n := by
  let U : Γ → Set B := fun a => (fun ξ : B => a⁻¹ • ξ) ⁻¹' Zᶜ
  have hopen (a : Γ) : IsOpen (U a) := hZ.isOpen_compl.preimage (continuous_const_smul a⁻¹)
  have hcover : (univ : Set B) ⊆ ⋃ a : Γ, U a := by
    intro ξ _
    obtain ⟨a, ha⟩ := hescape ξ
    exact mem_iUnion.mpr ⟨a, ha⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨F, fun ξ => ?_⟩
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hF (mem_univ ξ))
  obtain ⟨haF, hξ⟩ := mem_iUnion.mp ha
  exact ⟨a, haF, eventually_mem_of_shrinking_complements T Z hshrink hξ⟩

/-- Infinite orbits cannot remain inside a finite exceptional set. -/
theorem finite_corrected_eventual_cover_of_finite_exceptional_set
    {Γ B : Type*} [Group Γ] [TopologicalSpace B] [CompactSpace B] [T1Space B]
    [MulAction Γ B] [ContinuousConstSMul Γ B]
    (horbit : ∀ ξ : B, (MulAction.orbit Γ ξ).Infinite)
    (T : ℕ → Set B) {Z : Set B} (hZ : Z.Finite)
    (hshrink : ∀ U : Set B, IsOpen U → Z ⊆ U → ∀ᶠ n in atTop, (T n)ᶜ ⊆ U) :
    ∃ F : Finset Γ, ∀ ξ : B, ∃ a ∈ F, ∀ᶠ n in atTop, a⁻¹ • ξ ∈ T n := by
  apply finite_corrected_eventual_cover_of_shrinking_complements T Z hZ.isClosed ?_ hshrink
  intro ξ
  by_contra hnone
  push Not at hnone
  apply horbit ξ
  apply hZ.subset
  rintro η ⟨a, rfl⟩
  simpa only [inv_inv] using hnone a⁻¹

end Singularity
