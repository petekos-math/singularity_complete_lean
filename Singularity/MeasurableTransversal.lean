import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Finset.Lattice.Union

/-!
# Measurable selection from finitely many injective sheets

Removing fibers already represented in earlier sheets gives a measurable set
on which the projection is injective, with exactly the same image as the
original finite cover. No measurable-selection axiom is used.
-/

noncomputable section
open Set

namespace Singularity

/-- A finite measurable family of injective sheets has a measurable transversal. -/
theorem exists_measurable_injective_selection {X Y ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y) (hf : Measurable f)
    (U : ι → Set X) (t : Finset ι)
    (hU : ∀ i ∈ t, MeasurableSet (U i))
    (himage : ∀ i ∈ t, MeasurableSet (f '' U i))
    (hinj : ∀ i ∈ t, Set.InjOn f (U i)) :
    ∃ S : Set X, MeasurableSet S ∧ S ⊆ ⋃ i ∈ t, U i ∧ Set.InjOn f S ∧
      f '' S = ⋃ i ∈ t, f '' U i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, MeasurableSet.empty, by simp, Set.injOn_empty _, by simp⟩
  | @insert a t ha ih =>
    obtain ⟨S, hSm, hSU, hSi, hSf⟩ := ih
      (fun i hi => hU i (Finset.mem_insert_of_mem hi))
      (fun i hi => himage i (Finset.mem_insert_of_mem hi))
      (fun i hi => hinj i (Finset.mem_insert_of_mem hi))
    refine ⟨U a ∪ (S \ f ⁻¹' (f '' U a)),
      (hU a (Finset.mem_insert_self ..)).union
        (hSm.diff ((himage a (Finset.mem_insert_self ..)).preimage hf)), ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (hSU hx.1)
    · intro x hx y hy hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hinj a (Finset.mem_insert_self ..) hx hy hxy
      · exact (hy.2 ⟨x, hx, hxy⟩).elim
      · exact (hx.2 ⟨y, hy, hxy.symm⟩).elim
      · exact hSi hx.1 hy.1 hxy
    · simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
      ext y
      constructor
      · rintro ⟨x, hx | hx, rfl⟩
        · exact Or.inl ⟨x, hx, rfl⟩
        · exact Or.inr (hSf ▸ (show f x ∈ f '' S from ⟨x, hx.1, rfl⟩))
      · rintro (hy | hy)
        · obtain ⟨x, hx, rfl⟩ := hy
          exact ⟨x, Or.inl hx, rfl⟩
        · obtain ⟨x, hx, rfl⟩ := hSf.symm ▸ hy
          by_cases hxU : f x ∈ f '' U a
          · obtain ⟨z, hz, hzx⟩ := hxU
            exact ⟨z, Or.inl hz, hzx⟩
          · exact ⟨x, Or.inr ⟨hx, hxU⟩, rfl⟩

end Singularity
