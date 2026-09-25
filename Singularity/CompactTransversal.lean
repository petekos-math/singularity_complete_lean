import Singularity.MeasurableTransversal
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Relatively compact measurable transversals

A surjective local homeomorphism from a locally compact space onto a compact
space admits a measurable transversal contained in a compact set. Compactness
reduces the local sheets to a finite family; the finite selection lemma removes
all repeated fibers.
-/

noncomputable section
open Set Topology

namespace Singularity

/-- Select one point in every fiber, measurably and inside a compact set. -/
theorem exists_compact_measurable_transversal {X Y : Type*}
    [TopologicalSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : IsLocalHomeomorph f) (hsurj : Function.Surjective f) :
    ∃ S K : Set X, MeasurableSet S ∧ IsCompact K ∧ S ⊆ K ∧ Set.InjOn f S ∧
      f '' S = univ := by
  classical
  have hsheets (x : X) : ∃ U K : Set X, IsOpen U ∧ x ∈ U ∧ IsCompact K ∧
      U ⊆ K ∧ Set.InjOn f U := by
    obtain ⟨e, hxe, he⟩ := hf x
    obtain ⟨K, hK, hxK, hKe⟩ := exists_compact_subset e.open_source hxe
    refine ⟨interior K, K, isOpen_interior, hxK, hK, interior_subset, ?_⟩
    rw [he]
    exact e.injOn.mono (interior_subset.trans hKe)
  choose U K hU hxU hK hUK hinj using hsheets
  have hcover : (univ : Set Y) ⊆ ⋃ x : X, f '' U x := by
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    exact mem_iUnion.mpr ⟨x, x, hxU x, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => f '' U x) (fun x => hf.isOpenMap _ (hU x)) hcover
  obtain ⟨S, hSm, hSU, hSi, hSf⟩ := exists_measurable_injective_selection f
    hf.continuous.measurable U t (fun i _ => (hU i).measurableSet)
    (fun i _ => (hf.isOpenMap _ (hU i)).measurableSet) (fun i _ => hinj i)
  refine ⟨S, ⋃ i ∈ t, K i, hSm,
    t.isCompact_biUnion (fun i _ => hK i), ?_, hSi, ?_⟩
  · exact hSU.trans (iUnion₂_mono fun i _ => hUK i)
  · rw [hSf]
    exact eq_univ_iff_forall.mpr (fun y => ht (mem_univ y))

end Singularity
