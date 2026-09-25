import Singularity.CompactTransversal
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-!
# Finite fundamental domains for compact quotients

For a discrete subgroup of a locally compact Polish group with compact
quotient, local sheets give a measurable transversal contained in a compact
set. The free right action makes this a genuine fundamental domain. Every
locally finite Borel measure therefore gives it finite mass.
-/

noncomputable section
open Set MeasureTheory Topology

namespace Singularity

/-- A measurable transversal for the right cosets is a fundamental domain for the right action. -/
theorem isFundamentalDomain_of_quotient_transversal {G : Type*} [Group G]
    [MeasurableSpace G] (Γ : Subgroup G) (ν : Measure G) {S : Set G}
    (hS : MeasurableSet S) (hinj : Set.InjOn (QuotientGroup.mk : G → G ⧸ Γ) S)
    (himage : (QuotientGroup.mk : G → G ⧸ Γ) '' S = univ) :
    IsFundamentalDomain Γ.op S ν := by
  have hπ (γ : Γ.op) (x : G) :
      (QuotientGroup.mk (γ • x) : G ⧸ Γ) = QuotientGroup.mk x :=
    @Quotient.sound G (MulAction.orbitRel Γ.op G) _ _ ⟨γ, rfl⟩
  apply IsFundamentalDomain.mk' hS.nullMeasurableSet
  intro x
  obtain ⟨y, hy, hyx⟩ := (himage.symm ▸ mem_univ (QuotientGroup.mk x : G ⧸ Γ))
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact hyx))
  have hγS : γ • x ∈ S := by rw [hγ]; exact hy
  refine ⟨γ, hγS, ?_⟩
  intro δ hδ
  have he : δ • x = γ • x := hinj hδ hγS ((hπ δ x).trans (hπ γ x).symm)
  apply Subtype.ext
  apply MulOpposite.unop_injective
  exact mul_left_cancel he

/-- Compactness of a discrete coset quotient supplies a relatively compact measurable domain. -/
theorem exists_compact_fundamentalDomain {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
    [CompactSpace (G ⧸ Γ)] (ν : Measure G) :
    ∃ S K : Set G, MeasurableSet S ∧ IsCompact K ∧ S ⊆ K ∧
      IsFundamentalDomain Γ.op S ν := by
  have hc := (Γ.isQuotientCoveringMap ⟨inferInstance⟩).isCoveringMap.isLocalHomeomorph
  obtain ⟨S, K, hS, hK, hSK, hi, hs⟩ := exists_compact_measurable_transversal
    (QuotientGroup.mk : G → G ⧸ Γ) hc QuotientGroup.mk_surjective
  exact ⟨S, K, hS, hK, hSK, isFundamentalDomain_of_quotient_transversal Γ ν hS hi hs⟩

/-- The constructed domain has finite mass for every locally finite Borel measure. -/
theorem exists_finite_fundamentalDomain {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
    [CompactSpace (G ⧸ Γ)] (ν : Measure G) [IsLocallyFiniteMeasure ν] :
    ∃ S : Set G, MeasurableSet S ∧ IsFundamentalDomain Γ.op S ν ∧ ν S < ⊤ := by
  obtain ⟨S, K, hS, hK, hSK, hF⟩ := exists_compact_fundamentalDomain Γ ν
  exact ⟨S, hS, hF, (measure_mono hSK).trans_lt hK.measure_lt_top⟩

end Singularity
