import Singularity.InvariantSetDescent
import Singularity.QuotientErgodicity

/-!
# Transferring quotient-flow ergodicity to an endpoint action

A measurable endpoint map is invariant under one left time map and equivariant
for inverse right multiplication. If its pushforward has the same measure
class as the endpoint measure, ergodicity on the finite right-coset quotient
implies ergodicity of the lattice action on endpoints. Almost-invariant sets
are first replaced by exactly invariant representatives for the countable
lattice, so no pointwise invariance assumption is silently introduced.
-/

noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure

namespace Singularity

/-- Quotient-flow ergodicity implies ergodicity of the lattice endpoint action. -/
theorem ergodicSMul_of_quotient_flow {G X : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace X] [MulAction G X]
    (Γ : Subgroup G) [Countable Γ] (ν : Measure G)
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    (μ : Measure (G ⧸ Γ)) [QuotientMeasureEqMeasurePreimage ν μ]
    [MeasurableConstSMul G (G ⧸ Γ)] {F : Set G} (hF : IsFundamentalDomain Γ.op F ν)
    (κ : Measure X) [SMulInvariantMeasure Γ X κ]
    (f : G → X) (hf : Measurable f)
    (hclass : ν.map f ≪ κ ∧ κ ≪ ν.map f)
    (hequiv : ∀ g h : G, f (g * h) = h⁻¹ • f g)
    (a : G) (hflow : ∀ g, f (a * g) = f g)
    (herg : Ergodic (fun q : G ⧸ Γ => a • q) μ) : ErgodicSMul Γ X κ := by
  refine ⟨fun {s} hs hinv => ?_⟩
  have hqf : QuasiMeasurePreserving f ν κ := ⟨hf, hclass.1⟩
  have hright (γ : Γ.op) : (fun g : G => γ • g) ⁻¹' (f ⁻¹' s) =ᵐ[ν] f ⁻¹' s := by
    let δ : Γ := ⟨MulOpposite.unop (γ : Gᵐᵒᵖ), γ.property⟩
    filter_upwards [hqf.ae (hinv δ⁻¹).mem_iff] with g hg
    apply propext
    change f (g * (δ : G)) ∈ s ↔ f g ∈ s
    rw [hequiv]
    exact hg
  obtain ⟨t, htm, ht⟩ := exists_quotient_set_ae_eq (G := Γ.op) ν (hs.preimage hf) hright
  have hleft : ∀ᵐ g ∂ν, a • (QuotientGroup.mk g : G ⧸ Γ) ∈ t ↔
      (QuotientGroup.mk g : G ⧸ Γ) ∈ t := by
    filter_upwards [ht.mem_iff, (measurePreserving_mul_left ν a).quasiMeasurePreserving.ae ht.mem_iff]
      with g hg hag
    change (QuotientGroup.mk (a * g) : G ⧸ Γ) ∈ t ↔ (QuotientGroup.mk g : G ⧸ Γ) ∈ t
    change (QuotientGroup.mk (a * g) : G ⧸ Γ) ∈ t ↔ f (a * g) ∈ s at hag
    rw [hflow] at hag
    exact hag.trans hg.symm
  have hti : (fun q : G ⧸ Γ => a • q) ⁻¹' t =ᵐ[μ] t := by
    have h := (quotientMeasure_ae_iff Γ ν μ hF
      ((htm.preimage (measurable_const_smul a)).mem.iff htm.mem).setOf).mp hleft
    exact h.mono fun q hq => propext hq
  have htc : EventuallyConst t (ae μ) := herg.quasiErgodic.aeconst_set₀ htm.nullMeasurableSet hti
  have hgc : EventuallyConst (QuotientGroup.mk ⁻¹' t : Set G) (ae ν) := by
    rw [eventuallyConst_set] at htc ⊢
    rcases htc with htc | htc
    · exact Or.inl ((quotientMeasure_ae_iff Γ ν μ hF htm).mpr htc)
    · exact Or.inr ((quotientMeasure_ae_iff Γ ν μ hF htm.compl).mpr htc)
  have hfc : EventuallyConst (f ⁻¹' s : Set G) (ae ν) := hgc.congr ht
  rw [eventuallyConst_set] at hfc ⊢
  rcases hfc with hfc | hfc
  · exact Or.inl (hclass.2.ae_le ((ae_map_iff hf.aemeasurable hs).mpr hfc))
  · exact Or.inr (hclass.2.ae_le ((ae_map_iff hf.aemeasurable hs.compl).mpr hfc))

end Singularity
