import Mathlib.Dynamics.Ergodic.Action.Basic

/-!
# Zero–one property of a factor in the same measure class

The pushforward of an invariant ergodic measure can have infinite mass. Its
null sets nevertheless transfer ergodicity to a probability measure in the
same measure class, without asserting that probability measure is invariant.
-/

noncomputable section
open MeasureTheory Filter Set

namespace Singularity

/-- An equivariant measurable factor inherits the zero–one property across equivalent measure classes. -/
theorem invariant_zero_one_of_ergodic_factor
    {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]
    [MulAction G X] [MulAction G Y]
    (J : Measure X) [ErgodicSMul G X J] (m : Measure Y) [IsProbabilityMeasure m]
    (f : X → Y) (hf : Measurable f)
    (hclass : J.map f ≪ m ∧ m ≪ J.map f)
    (heq : ∀ g : G, ∀ x : X, f (g • x) = g • f x)
    {E : Set Y} (hE : MeasurableSet E)
    (hinv : ∀ g : G, (fun y : Y => g • y) ⁻¹' E =ᵐ[m] E) :
    m E = 0 ∨ m E = 1 := by
  have hconst : EventuallyConst (f ⁻¹' E) (ae J) := by
    apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G := G) (hE.preimage hf)
    intro g
    have h := ae_of_ae_map hf.aemeasurable (hclass.1.ae_le (hinv g).mem_iff)
    filter_upwards [h] with x hx
    apply propext
    simpa only [mem_preimage, heq] using hx
  rw [eventuallyConst_set] at hconst
  rcases hconst with h | h
  · right
    apply (mem_ae_iff_prob_eq_one hE).mp
    exact hclass.2.ae_le ((ae_map_iff hf.aemeasurable hE).mpr h)
  · left
    have h' := hclass.2.ae_le ((ae_map_iff hf.aemeasurable hE.compl).mpr h)
    have h'' : ∀ᵐ y ∂m, y ∉ E := h'
    simpa only [not_not, ofPred_mem_eq] using (ae_iff.mp h'')

end Singularity
