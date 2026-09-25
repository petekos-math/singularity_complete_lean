import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Algebra.Group.Action.Pretransitive

/-!
# The measure class of a homogeneous orbit map

For a transitive measurable group action preserving a nonzero sigma-finite
measure, the orbit pushforward of a nonzero sigma-finite right-invariant group
measure has exactly the same null sets. Right invariance makes the orbit
pushforward independent of the base point, and Fubini proves both directions.
-/

noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure

namespace Singularity

/-- Right invariance makes the measures of orbit preimages independent of the base point. -/
theorem orbit_preimage_measure_eq {G X : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] [MulAction G X] [MulAction.IsPretransitive G X]
    (ν : Measure G) [ν.IsMulRightInvariant] (x y : X) (s : Set X) :
    ν ((fun g : G => g • x) ⁻¹' s) = ν ((fun g : G => g • y) ⁻¹' s) := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G x y
  have h := measure_preimage_mul_right ν a ((fun g : G => g • x) ⁻¹' s)
  simpa only [preimage_preimage, Function.comp_def, mul_smul] using h.symm

/-- A homogeneous orbit map detects precisely the null sets of an invariant measure. -/
theorem orbit_preimage_null_iff {G X : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace X]
    [MulAction G X] [MulAction.IsPretransitive G X] [MeasurableSMul₂ G X]
    (ν : Measure G) [SFinite ν] [NeZero ν] [ν.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ] [NeZero μ] [SMulInvariantMeasure G X μ]
    (x : X) {s : Set X} (hs : MeasurableSet s) :
    ν ((fun g : G => g • x) ⁻¹' s) = 0 ↔ μ s = 0 := by
  have hmeas : MeasurableSet {p : G × X | p.1 • p.2 ∉ s} :=
    (hs.preimage (measurable_fst.smul measurable_snd)).compl
  constructor
  · intro hzero
    have hx (y : X) : ∀ᵐ g ∂ν, g • y ∉ s := by
      have hy := (orbit_preimage_measure_eq ν x y s).symm.trans hzero
      simpa only [ae_iff, not_not, Set.preimage] using hy
    have hg : ∀ᵐ g ∂ν, ∀ᵐ y ∂μ, g • y ∉ s :=
      (ae_ae_comm hmeas).mpr (ae_of_all _ hx)
    obtain ⟨g, hg⟩ := hg.exists
    have hz : μ ((fun y => g • y) ⁻¹' s) = 0 := by
      simpa only [ae_iff, not_not, Set.preimage] using hg
    rwa [SMulInvariantMeasure.measure_preimage_smul g hs] at hz
  · intro hzero
    have hg (g : G) : ∀ᵐ y ∂μ, g • y ∉ s := by
      have hz : μ ((fun y => g • y) ⁻¹' s) = 0 := by
        rw [SMulInvariantMeasure.measure_preimage_smul g hs, hzero]
      simpa only [ae_iff, not_not, Set.preimage] using hz
    have hx : ∀ᵐ y ∂μ, ∀ᵐ g ∂ν, g • y ∉ s :=
      (ae_ae_comm hmeas).mp (ae_of_all _ hg)
    obtain ⟨y, hy⟩ := hx.exists
    have hz : ν ((fun g : G => g • y) ⁻¹' s) = 0 := by
      simpa only [ae_iff, not_not, Set.preimage] using hy
    exact (orbit_preimage_measure_eq ν x y s).trans hz

/-- The homogeneous orbit pushforward and the invariant measure are mutually absolutely continuous. -/
theorem orbit_map_measureClass {G X : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace X]
    [MulAction G X] [MulAction.IsPretransitive G X] [MeasurableSMul₂ G X]
    (ν : Measure G) [SFinite ν] [NeZero ν] [ν.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ] [NeZero μ] [SMulInvariantMeasure G X μ] (x : X) :
    (ν.map (fun g : G => g • x)) ≪ μ ∧ μ ≪ (ν.map (fun g : G => g • x)) := by
  have hm : Measurable (fun g : G => g • x) := measurable_id.smul measurable_const
  constructor
  · apply AbsolutelyContinuous.mk
    intro s hs hzero
    rw [Measure.map_apply hm hs]
    exact (orbit_preimage_null_iff ν μ x hs).mpr hzero
  · apply AbsolutelyContinuous.mk
    intro s hs hzero
    rw [Measure.map_apply hm hs] at hzero
    exact (orbit_preimage_null_iff ν μ x hs).mp hzero

/-- The same measure-class statement for the inverse orbit map and a left-invariant measure. -/
theorem inverse_orbit_map_measureClass {G X : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace X]
    [MulAction G X] [MulAction.IsPretransitive G X] [MeasurableSMul₂ G X]
    (ν : Measure G) [SFinite ν] [NeZero ν] [ν.IsMulLeftInvariant]
    (μ : Measure X) [SFinite μ] [NeZero μ] [SMulInvariantMeasure G X μ] (x : X) :
    (ν.map (fun g : G => g⁻¹ • x)) ≪ μ ∧ μ ≪ (ν.map (fun g : G => g⁻¹ • x)) := by
  let : NeZero ν.inv := ⟨(Measure.map_ne_zero_iff measurable_inv.aemeasurable).mpr (NeZero.ne ν)⟩
  have hm : Measurable (fun g : G => g • x) := measurable_id.smul measurable_const
  have h := orbit_map_measureClass ν.inv μ x
  rw [Measure.inv, Measure.map_map hm measurable_inv] at h
  exact h

end Singularity
