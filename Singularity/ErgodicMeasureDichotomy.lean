import Singularity.InvariantSetDescent
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-!
# Absolute continuity or singularity for an ergodic measure

For a countable group, if the reference measure is quasi-invariant, every
reference-null set has a reference-null invariant saturation. The zero–one
property of a probability measure therefore excludes a nonzero singular part
unless the whole measure is singular. No invariant-measure hypothesis is imposed
on that probability measure.
-/

noncomputable section
open MeasureTheory Set Filter

namespace Singularity

/-- An ergodic probability measure not singular to a quasi-invariant reference is absolutely continuous. -/
theorem absolutelyContinuous_of_invariant_zero_one
    {G X : Type*} [Group G] [Countable G] [MeasurableSpace X]
    [MulAction G X] [MeasurableConstSMul G X]
    (ν m : Measure X) [IsProbabilityMeasure ν]
    (hm : ∀ g : G, Measure.map (fun x : X => g • x) m ≪ m)
    (herg : ∀ E : Set X, MeasurableSet E →
      (∀ g : G, (fun x : X => g • x) ⁻¹' E =ᵐ[ν] E) → ν E = 0 ∨ ν E = 1)
    (hns : ¬ ν ⟂ₘ m) : ν ≪ m := by
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hmS
  let T := (invariantSetCore G X Sᶜ)ᶜ
  have hT : MeasurableSet T := (invariantSetCore_measurable hS.compl).compl
  have hsub : S ⊆ T := by
    intro x hx hxc
    have hc := (mem_iInter.mp hxc) (1 : G)
    exact hc (by simpa only [one_smul] using hx)
  have hmT : m T = 0 := by
    have he : T = ⋃ g : G, (fun x : X => g • x) ⁻¹' S := by
      simp only [T, invariantSetCore, compl_iInter, ← preimage_compl, compl_compl]
    rw [he]
    apply measure_iUnion_null
    intro g
    rw [← Measure.map_apply (measurable_const_smul g) hS]
    exact hm g hmS
  have hInv : ∀ g : G, (fun x : X => g • x) ⁻¹' T = T := by
    intro g
    simp only [T, preimage_compl, preimage_invariantSetCore]
  rcases herg T hT (fun g => Filter.EventuallyEq.of_eq (hInv g)) with h0 | h1
  · exact measure_mono_null hsub h0
  · exfalso
    apply hns
    refine ⟨Tᶜ, hT.compl, ?_, ?_⟩
    · rw [measure_compl hT (measure_ne_top ν T), h1, measure_univ, tsub_self]
    · simpa only [compl_compl] using hmT

end Singularity
