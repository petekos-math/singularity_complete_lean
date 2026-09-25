import Singularity.RadonNikodymCoboundary

/-!
# Restriction to an invariant measure carrier

Restricting both an absolutely continuous measure and its reference preserves
their derivative on the restricted space. For an invariant set, translation
commutes with restriction, so the actual logarithmic cocycle is unchanged.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

/-- Restricting both measures preserves their derivative on the restriction. -/
theorem rnDeriv_restrict_both_of_absolutelyContinuous {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) [SigmaFinite ν] [SigmaFinite m] (hac : ν ≪ m)
    {E : Set B} (hE : MeasurableSet E) :
    (ν.restrict E).rnDeriv (m.restrict E) =ᵐ[m.restrict E] ν.rnDeriv m := by
  have he : (m.restrict E).withDensity (ν.rnDeriv m) = ν.restrict E := by
    rw [← restrict_withDensity hE, Measure.withDensity_rnDeriv_eq _ _ hac]
  rw [← he]
  exact Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)

/-- A measure carried by E has the same density relative to the original
reference and its restriction, almost everywhere for the original measure. -/
theorem rnDeriv_restrict_reference_of_conull {B : Type*} [MeasurableSpace B]
    (ν m : Measure B) [SigmaFinite ν] [SigmaFinite m] (hac : ν ≪ m)
    {E : Set B} (hE : MeasurableSet E) (hfull : ∀ᵐ ξ ∂ν, ξ ∈ E) :
    ν.rnDeriv (m.restrict E) =ᵐ[ν] ν.rnDeriv m := by
  have hr := rnDeriv_restrict_both_of_absolutelyContinuous ν m hac hE
  have hacE := hac.restrict E
  rw [Measure.restrict_eq_self_of_ae_mem hfull] at hr hacE
  exact hacE.ae_le hr

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B]

/-- Translation commutes with restriction to an invariant measurable set. -/
theorem map_smul_invariant_restrict (m : Measure B) {E : Set B} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E = E) (g : Γ) :
    Measure.map (fun ξ : B => g • ξ) (m.restrict E) =
      (Measure.map (fun ξ : B => g • ξ) m).restrict E := by
  rw [Measure.restrict_map (measurable_const_smul g) hE, hinv g]

/-- Restriction to an invariant set preserves quasi-invariance. -/
theorem invariant_restrict_quasiInvariant (m : Measure B) {E : Set B} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E = E)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) m ≪ m) (g : Γ) :
    Measure.map (fun ξ : B => g • ξ) (m.restrict E) ≪ m.restrict E := by
  rw [map_smul_invariant_restrict m hE hinv g]
  exact (hq g).restrict E

/-- The translated density is unchanged by invariant restriction. -/
theorem stationaryDensity_invariant_restrict (m : Measure B) [IsFiniteMeasure m]
    {E : Set B} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E = E)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) m ≪ m) (g : Γ) :
    stationaryDensity (m.restrict E) g =ᵐ[m.restrict E] stationaryDensity m g := by
  unfold stationaryDensity
  rw [map_smul_invariant_restrict m hE hinv g]
  exact rnDeriv_restrict_both_of_absolutelyContinuous _ _ (hq g) hE

/-- The actual logarithmic cocycle is unchanged on an invariant carrier. -/
theorem stationaryLogCocycle_invariant_restrict (m : Measure B) [IsFiniteMeasure m]
    {E : Set B} (hE : MeasurableSet E)
    (hinv : ∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E = E)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) m ≪ m) (g : Γ) :
    stationaryLogCocycle (m.restrict E) g =ᵐ[m.restrict E] stationaryLogCocycle m g := by
  filter_upwards [stationaryDensity_invariant_restrict m hE hinv hq g⁻¹] with ξ hξ
  simp only [stationaryLogCocycle, stationaryRealDensity, hξ]

end Singularity
