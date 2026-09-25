import Singularity.StripSeparation

/-!
# Enlarging a finite separator to control outgoing steps

A step can first encounter a separator at its terminal vertex. Adding all
one-step predecessors makes every step leaving a side start in the enlarged
finite set. This is the trapping condition used for infinite sample paths.
-/

noncomputable section
open Set
open scoped Classical
namespace Singularity

/-- Adding finitely many predecessors turns avoidance at both ends of a
step into an outgoing-exit condition depending only on its initial vertex. -/
theorem exists_finite_exit_enlargement {Γ : Type*} [Group Γ]
    (s A : Finset Γ) (V : Set Γ)
    (hstep : ∀ v : Γ, v ∉ (A : Set Γ) → ∀ t ∈ s,
      v * t ∉ (A : Set Γ) → v ∈ V → v * t ∈ V) :
    ∃ T : Finset Γ, A ⊆ T ∧ ∀ v ∈ V, v ∉ (T : Set Γ) → ∀ t ∈ s, v * t ∈ V := by
  let T := A ∪ s.biUnion (fun t => A.image (fun a => a * t⁻¹))
  have hAT : A ⊆ T := Finset.subset_union_left
  refine ⟨T, hAT, fun v hv hnot t ht => ?_⟩
  apply hstep v (fun ha => hnot (hAT ha)) t ht ?_ hv
  intro hvt
  apply hnot
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨t, ht, Finset.mem_image.mpr ⟨v * t, hvt, ?_⟩⟩
  simp

end Singularity
