import Singularity.InvariantSetDescent

/-!
# Common invariant domains for almost-everywhere identities

For a countable quasi-invariant action, every measurable conull set contains
a measurable invariant conull set. This permits simultaneous pointwise use
of countably many Radon–Nikodym identities without changing their meaning.
-/

noncomputable section
open MeasureTheory Set Filter

namespace Singularity

/-- The identity translate shows that the invariant core is a subset of the original set. -/
theorem invariantSetCore_subset {G X : Type*} [Group G] [MulAction G X] (E : Set X) :
    invariantSetCore G X E ⊆ E := by
  intro x hx
  simpa only [mem_preimage, one_smul] using (mem_iInter.mp hx) (1 : G)

/-- Every translate of a conull set is conull for a quasi-invariant action;
therefore the countable invariant core is conull. -/
theorem invariantSetCore_conull {G X : Type*} [Group G] [Countable G]
    [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
    (ν : Measure X) (hq : ∀ g : G, Measure.map (fun x : X => g • x) ν ≪ ν)
    {E : Set X} (hE : ∀ᵐ x ∂ν, x ∈ E) :
    ∀ᵐ x ∂ν, x ∈ invariantSetCore G X E := by
  have hall : ∀ᵐ x ∂ν, ∀ g : G, g • x ∈ E := by
    apply ae_all_iff.mpr
    intro g
    exact (show Measure.QuasiMeasurePreserving (fun x : X => g • x) ν ν from
      ⟨measurable_const_smul g, hq g⟩).ae hE
  simpa only [invariantSetCore, mem_iInter, mem_preimage] using hall

/-- A measurable conull set contains an exactly invariant measurable conull set. -/
theorem exists_invariant_conull_subset {G X : Type*} [Group G] [Countable G]
    [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
    (ν : Measure X) (hq : ∀ g : G, Measure.map (fun x : X => g • x) ν ≪ ν)
    {E : Set X} (hE : MeasurableSet E) (hfull : ∀ᵐ x ∂ν, x ∈ E) :
    ∃ F : Set X, MeasurableSet F ∧ (∀ᵐ x ∂ν, x ∈ F) ∧ F ⊆ E ∧
      ∀ g : G, (fun x : X => g • x) ⁻¹' F = F :=
  ⟨invariantSetCore G X E, invariantSetCore_measurable hE,
    invariantSetCore_conull ν hq hfull, invariantSetCore_subset E,
    fun g => preimage_invariantSetCore E g⟩

end Singularity
