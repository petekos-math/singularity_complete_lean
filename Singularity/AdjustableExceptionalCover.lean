import Singularity.ShrinkingExceptionalSets
import Mathlib.Topology.Separation.Regular

/-!
# Finite correction covers after enlarging shadows

A neighborhood of a closed exceptional set can be avoided by finitely many
corrections if no orbit is contained in the exceptional set. Consequently,
when enlarging shadows makes inverse complements approach that set, one
fixed sufficiently large parameter gives a finite eventual cover.
-/

noncomputable section
open Set Filter
open scoped Classical Topology

namespace Singularity

/-- Orbit escape persists on a neighborhood of a closed exceptional set,
with a finite list of correcting elements valid over the whole compact space. -/
theorem finite_corrections_avoid_exceptional_neighborhood
    {Γ B : Type*} [Group Γ] [TopologicalSpace B] [CompactSpace B] [RegularSpace B]
    [MulAction Γ B] [ContinuousConstSMul Γ B]
    (Z : Set B) (hZ : IsClosed Z)
    (hescape : ∀ ξ : B, ∃ a : Γ, a⁻¹ • ξ ∉ Z) :
    ∃ U : Set B, IsOpen U ∧ Z ⊆ U ∧ ∃ F : Finset Γ,
      ∀ ξ : B, ∃ a ∈ F, a⁻¹ • ξ ∉ U := by
  choose a ha using hescape
  have hv (ξ : B) : ∃ V : Set B, (a ξ)⁻¹ • ξ ∈ V ∧ IsOpen V ∧ closure V ⊆ Zᶜ := by
    obtain ⟨V, ⟨hx, ho⟩, hc⟩ := (hasBasis_opens_closure ((a ξ)⁻¹ • ξ)).mem_iff.mp
      (hZ.isOpen_compl.mem_nhds (ha ξ))
    exact ⟨V, hx, ho, hc⟩
  choose V hxV hV hcl using hv
  let W : B → Set B := fun ξ => (fun η : B => (a ξ)⁻¹ • η) ⁻¹' V ξ
  have hW (ξ : B) : IsOpen (W ξ) := (hV ξ).preimage (continuous_const_smul (a ξ)⁻¹)
  have hc : (univ : Set B) ⊆ ⋃ ξ : B, W ξ := by
    intro ξ _
    exact mem_iUnion.mpr ⟨ξ, hxV ξ⟩
  obtain ⟨P, hP⟩ := isCompact_univ.elim_finite_subcover W hW hc
  let U : Set B := (⋃ ξ ∈ P, closure (V ξ))ᶜ
  refine ⟨U, ?_, ?_, P.image a, fun η => ?_⟩
  · exact (isClosed_biUnion_finset (fun ξ _ => isClosed_closure)).isOpen_compl
  · intro η hη hbad
    obtain ⟨ξ, hξ⟩ := mem_iUnion.mp hbad
    obtain ⟨_, hmem⟩ := mem_iUnion.mp hξ
    exact hcl ξ hmem hη
  · obtain ⟨ξ, hξ⟩ := mem_iUnion.mp (hP (mem_univ η))
    obtain ⟨hξP, hη⟩ := mem_iUnion.mp hξ
    refine ⟨a ξ, Finset.mem_image.mpr ⟨ξ, hξP, rfl⟩, fun hbad => ?_⟩
    exact hbad (mem_iUnion.mpr ⟨ξ, mem_iUnion.mpr ⟨hξP, subset_closure hη⟩⟩)

/-- The shadow parameter is chosen before the eventual cover. The inverse
complements need only approach the exceptional set after enlarging shadows. -/
theorem finite_eventual_cover_of_adjustable_shadows
    {Γ B I : Type*} [Group Γ] [TopologicalSpace B] [CompactSpace B] [RegularSpace B]
    [MulAction Γ B] [ContinuousConstSMul Γ B]
    (T : I → ℕ → Set B) (Z : Set B) (hZ : IsClosed Z)
    (hescape : ∀ ξ : B, ∃ a : Γ, a⁻¹ • ξ ∉ Z)
    (hshrink : ∀ U : Set B, IsOpen U → Z ⊆ U → ∃ i : I,
      ∀ᶠ n in atTop, (T i n)ᶜ ⊆ U) :
    ∃ i : I, ∃ F : Finset Γ, ∀ ξ : B, ∃ a ∈ F, ∀ᶠ n in atTop, a⁻¹ • ξ ∈ T i n := by
  obtain ⟨U, hU, hZU, F, hF⟩ := finite_corrections_avoid_exceptional_neighborhood Z hZ hescape
  obtain ⟨i, hi⟩ := hshrink U hU hZU
  refine ⟨i, F, fun ξ => ?_⟩
  obtain ⟨a, ha, hnot⟩ := hF ξ
  refine ⟨a, ha, ?_⟩
  filter_upwards [hi] with n hn
  by_contra hbad
  exact hnot (hn hbad)

end Singularity
