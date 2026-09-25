import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Descending almost-invariant sets to an orbit quotient

For a countable group, intersecting all translates of an almost-invariant
measurable set gives an exactly invariant measurable representative in the
same measure class. Its image is measurable in the quotient sigma algebra,
so no measurable choice of coset representatives is required.
-/

noncomputable section
open Set Filter MeasureTheory

namespace Singularity

/-- The largest invariant subset obtained by intersecting all inverse translates. -/
def invariantSetCore (G X : Type*) [SMul G X] (s : Set X) : Set X :=
  ⋂ g : G, (fun x : X => g • x) ⁻¹' s

/-- Group translation preserves the core exactly. -/
theorem preimage_invariantSetCore {G X : Type*} [Group G] [MulAction G X]
    (s : Set X) (g : G) :
    (fun x : X => g • x) ⁻¹' invariantSetCore G X s = invariantSetCore G X s := by
  ext x
  simp only [invariantSetCore, mem_preimage, mem_iInter]
  constructor
  · intro h a
    simpa only [mul_smul, inv_smul_smul] using h (a * g⁻¹)
  · intro h a
    simpa only [mul_smul] using h (a * g)

theorem invariantSetCore_measurable {G X : Type*} [Countable G] [SMul G X]
    [MeasurableSpace X] [MeasurableConstSMul G X] {s : Set X} (hs : MeasurableSet s) :
    MeasurableSet (invariantSetCore G X s) :=
  MeasurableSet.iInter (fun g => hs.preimage (measurable_const_smul g))

/-- Countably many almost-invariances give an exactly invariant representative. -/
theorem invariantSetCore_ae_eq {G X : Type*} [Group G] [MulAction G X] [Countable G]
    [MeasurableSpace X] (μ : Measure X) (s : Set X)
    (hinv : ∀ g : G, (fun x : X => g • x) ⁻¹' s =ᵐ[μ] s) :
    invariantSetCore G X s =ᵐ[μ] s := by
  have h : ∀ᵐ x ∂μ, ∀ g : G, (g • x ∈ s ↔ x ∈ s) :=
    ae_all_iff.mpr (fun g => (hinv g).mem_iff)
  filter_upwards [h] with x hx
  apply propext
  simp only [invariantSetCore, mem_iInter, mem_preimage]
  exact ⟨fun h => by simpa only [one_smul] using h 1, fun h g => (hx g).mpr h⟩

/-- Saturating the core adds no new points. -/
theorem quotient_preimage_image_invariantSetCore {G X : Type*} [Group G] [MulAction G X]
    (s : Set X) :
    Quotient.mk (MulAction.orbitRel G X) ⁻¹'
      (Quotient.mk (MulAction.orbitRel G X) '' invariantSetCore G X s) = invariantSetCore G X s := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hyx))
    rw [← hg] at hy
    change x ∈ (fun z : X => g • z) ⁻¹' invariantSetCore G X s at hy
    rwa [preimage_invariantSetCore] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- An almost-invariant measurable set descends, modulo null sets, to a measurable quotient set. -/
theorem exists_quotient_set_ae_eq {G X : Type*} [Group G] [MulAction G X] [Countable G]
    [MeasurableSpace X] [MeasurableConstSMul G X] (μ : Measure X)
    {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (fun x : X => g • x) ⁻¹' s =ᵐ[μ] s) :
    ∃ t : Set (Quotient (MulAction.orbitRel G X)), MeasurableSet t ∧
      Quotient.mk (MulAction.orbitRel G X) ⁻¹' t =ᵐ[μ] s := by
  refine ⟨Quotient.mk (MulAction.orbitRel G X) '' invariantSetCore G X s, ?_, ?_⟩
  · apply measurableSet_quotient.mpr
    change MeasurableSet (Quotient.mk (MulAction.orbitRel G X) ⁻¹'
      (Quotient.mk (MulAction.orbitRel G X) '' invariantSetCore G X s))
    rw [quotient_preimage_image_invariantSetCore]
    exact invariantSetCore_measurable hs
  · rw [quotient_preimage_image_invariantSetCore]
    exact invariantSetCore_ae_eq μ s hinv

end Singularity
