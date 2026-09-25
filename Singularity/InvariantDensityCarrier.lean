import Singularity.InvariantConullSet
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# An invariant carrier on which two measure classes agree

If a quasi-invariant finite measure is absolutely continuous with respect to
a reference measure, one can restrict the latter to an invariant conull
carrier to obtain equivalent measures. This does not assert equivalence with
the unrestricted reference measure.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

/-- Restricting to a set where the Radon–Nikodym density is positive gives
absolute continuity back toward the original measure. -/
theorem restrict_absolutelyContinuous_of_rnDeriv_pos {X : Type*} [MeasurableSpace X]
    (ν m : Measure X) [SigmaFinite ν] [SigmaFinite m]
    {E : Set X} (hE : MeasurableSet E) (hp : ∀ x ∈ E, 0 < ν.rnDeriv m x) :
    m.restrict E ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hνS
  have hν : ∀ᵐ x ∂ν, x ∉ S := by simpa [ae_iff] using hνS
  have hm := Measure.ae_rnDeriv_ne_zero_imp_of_ae m hν
  have ht : ∀ᵐ x ∂m.restrict E, x ∉ S := by
    apply (ae_restrict_iff' hE).mpr
    filter_upwards [hm] with x hx hEx
    exact hx (hp x hEx).ne'
  simpa [ae_iff] using ht

/-- Absolute continuity admits an invariant full-measure carrier on which the
restricted reference and original measure have precisely the same null sets. -/
theorem exists_invariant_equivalent_restriction
    {Γ X : Type*} [Group Γ] [Countable Γ] [MeasurableSpace X]
    [MulAction Γ X] [MeasurableConstSMul Γ X]
    (ν m : Measure X) [SigmaFinite ν] [SigmaFinite m] (hac : ν ≪ m)
    (hq : ∀ g : Γ, Measure.map (fun x : X => g • x) ν ≪ ν) :
    ∃ E : Set X, MeasurableSet E ∧ (∀ᵐ x ∂ν, x ∈ E) ∧
      (∀ g : Γ, (fun x : X => g • x) ⁻¹' E = E) ∧
      (ν ≪ m.restrict E) ∧ (m.restrict E ≪ ν) ∧
      ∀ x ∈ E, 0 < ν.rnDeriv m x ∧ ν.rnDeriv m x < ∞ := by
  have hm : MeasurableSet {x | 0 < ν.rnDeriv m x ∧ ν.rnDeriv m x < ∞} :=
    (measurableSet_lt measurable_const (Measure.measurable_rnDeriv ν m)).inter
      (measurableSet_lt (Measure.measurable_rnDeriv ν m) measurable_const)
  have hp : ∀ᵐ x ∂ν, 0 < ν.rnDeriv m x ∧ ν.rnDeriv m x < ∞ :=
    (Measure.rnDeriv_pos hac).and (hac.ae_le (Measure.rnDeriv_lt_top ν m))
  obtain ⟨E, hE, hfull, hsub, hinv⟩ := exists_invariant_conull_subset ν hq hm hp
  refine ⟨E, hE, hfull, hinv, ?_, ?_, fun x hx => hsub hx⟩
  · have h := hac.restrict E
    rwa [Measure.restrict_eq_self_of_ae_mem hfull] at h
  · exact restrict_absolutelyContinuous_of_rnDeriv_pos ν m hE (fun x hx => (hsub hx).1)

end Singularity
