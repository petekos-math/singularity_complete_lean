import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-!
# Ergodicity of the full group on a quotient

A fundamental domain identifies null sets in a quotient with null sets of
their full preimages. This transfers ergodicity of the regular Haar action
to the quotient action. No ergodicity of a diagonal subgroup is assumed.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Pointwise

namespace Singularity

/-- Null sets for a quotient measure are exactly the sets with Haar-null full preimage. -/
theorem quotientMeasure_null_iff {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [ν.IsMulRightInvariant] (μ : Measure (G ⧸ Γ))
    [QuotientMeasureEqMeasurePreimage ν μ] {F : Set G}
    (hF : IsFundamentalDomain Γ.op F ν) {s : Set (G ⧸ Γ)} (hs : MeasurableSet s) :
    μ s = 0 ↔ ν (QuotientGroup.mk ⁻¹' s) = 0 := by
  rw [hF.projection_respects_measure_apply μ hs]
  constructor
  · intro h
    apply hF.measure_zero_of_invariant _ _ h
    intro γ
    ext x
    simp only [mem_smul_set_iff_inv_smul_mem, mem_preimage]
    have heq : Quotient.mk (MulAction.orbitRel Γ.op G) (γ⁻¹ • x) =
        Quotient.mk (MulAction.orbitRel Γ.op G) x := Quotient.sound ⟨γ⁻¹, rfl⟩
    exact heq ▸ Iff.rfl
  · intro h
    exact measure_mono_null inter_subset_left h

/-- Almost-everywhere assertions can be checked on the full group above a quotient. -/
theorem quotientMeasure_ae_iff {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [ν.IsMulRightInvariant] (μ : Measure (G ⧸ Γ))
    [QuotientMeasureEqMeasurePreimage ν μ] {F : Set G}
    (hF : IsFundamentalDomain Γ.op F ν) {P : (G ⧸ Γ) → Prop}
    (hP : MeasurableSet {x | P x}) :
    (∀ᵐ x ∂ν, P (QuotientGroup.mk x)) ↔ ∀ᵐ x ∂μ, P x := by
  simp only [ae_iff]
  exact (quotientMeasure_null_iff Γ ν μ hF hP.compl).symm

/-- The full group action on a Haar quotient is ergodic. -/
theorem ergodicSMul_quotient_of_fundamentalDomain {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (ν : Measure G) [SFinite ν]
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (μ : Measure (G ⧸ Γ))
    [QuotientMeasureEqMeasurePreimage ν μ] [SMulInvariantMeasure G (G ⧸ Γ) μ]
    [MeasurableConstSMul G (G ⧸ Γ)] {F : Set G}
    (hF : IsFundamentalDomain Γ.op F ν) : ErgodicSMul G (G ⧸ Γ) μ := by
  refine ⟨fun {s} hs hinv => ?_⟩
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := by
    exact measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  have he : EventuallyConst (QuotientGroup.mk ⁻¹' s : Set G) (ae ν) := by
    apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G := G) (hs.preimage hπ)
    intro g
    have hh := (quotientMeasure_ae_iff Γ ν μ hF
      ((hs.preimage (measurable_const_smul g)).mem.iff hs.mem).setOf).mpr (hinv g).mem_iff
    filter_upwards [hh] with x hx
    exact propext hx
  rw [eventuallyConst_set] at he ⊢
  rcases he with he | he
  · exact Or.inl ((quotientMeasure_ae_iff Γ ν μ hF hs).mp he)
  · exact Or.inr ((quotientMeasure_ae_iff Γ ν μ hF hs.compl).mp he)

end Singularity
