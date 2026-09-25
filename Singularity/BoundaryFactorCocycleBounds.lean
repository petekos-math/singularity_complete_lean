import Singularity.CocycleDeficitShadows
import Singularity.VisualShadowDensity

/-!
# Local cocycle bounds descend through boundary factors

An equivariant measurable factor need not be injective. Local upper bounds
on inverse-translate densities nevertheless descend, by measure domination.
Equivalently, local lower bounds for the forward logarithmic cocycle descend
with the same constants. No identity of pointwise derivatives is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace Singularity

variable {Γ B C : Type*} [Group Γ]
  [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
  [MeasurableSpace C] [MulAction Γ C] [MeasurableConstSMul Γ C]

/-- Equivariance intertwines actual translated pushforward measures. -/
theorem boundaryFactor_map_translate (ν : Measure B) (π : B → C)
    (hπ : Measurable π) (heq : ∀ g : Γ, ∀ ξ, π (g • ξ) = g • π ξ) (g : Γ) :
    Measure.map π (Measure.map (fun ξ : B => g • ξ) ν) =
      Measure.map (fun ξ : C => g • ξ) (Measure.map π ν) := by
  rw [Measure.map_map hπ (measurable_const_smul g),
    Measure.map_map (measurable_const_smul g) hπ]
  congr 1
  funext ξ
  exact heq g ξ

/-- The factor of a quasi-invariant measure is quasi-invariant. -/
theorem boundaryFactor_quasiInvariant (ν : Measure B) (π : B → C)
    (hπ : Measurable π) (heq : ∀ g : Γ, ∀ ξ, π (g • ξ) = g • π ξ)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν) (g : Γ) :
    Measure.map (fun ξ : C => g • ξ) (Measure.map π ν) ≪ Measure.map π ν := by
  rw [← boundaryFactor_map_translate ν π hπ heq g]
  exact (hq g).map hπ

/-- A local deficit bound upstairs gives the same bound downstairs, even
when distinct boundary points are identified by the factor. -/
theorem boundaryFactor_cocycle_deficit_bound (ν : Measure B) [IsFiniteMeasure ν]
    (π : B → C) (hπ : Measurable π)
    (heq : ∀ g : Γ, ∀ ξ, π (g • ξ) = g • π ξ)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)
    (g : Γ) (D R : ℝ) {E : Set C} (hE : MeasurableSet E)
    (hbound : ∀ᵐ ξ ∂ν, π ξ ∈ E → D - stationaryLogCocycle ν g ξ ≤ R) :
    ∀ᵐ η ∂Measure.map π ν, η ∈ E →
      D - stationaryLogCocycle (Measure.map π ν) g η ≤ R := by
  have hdom : (Measure.map (fun ξ : B => g⁻¹ • ξ) ν).restrict (π ⁻¹' E) ≤
      ENNReal.ofReal (Real.exp (R - D)) • ν := by
    rw [← Measure.withDensity_rnDeriv_eq _ _ (hq g⁻¹), restrict_withDensity (hE.preimage hπ), ← withDensity_indicator (hE.preimage hπ),
      ← withDensity_const]
    apply withDensity_mono
    filter_upwards [hbound, exp_neg_stationaryLogCocycle ν hq g] with ξ hb hexp
    by_cases hξ : π ξ ∈ E
    · rw [indicator_of_mem (show ξ ∈ π ⁻¹' E from hξ)]
      change stationaryDensity ν g⁻¹ ξ ≤ _
      rw [← hexp]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hb hξ]))
    · rw [indicator_of_notMem (show ξ ∉ π ⁻¹' E from hξ)]
      exact bot_le
  have hdown : (Measure.map (fun η : C => g⁻¹ • η) (Measure.map π ν)).restrict E ≤
      ENNReal.ofReal (Real.exp (R - D)) • Measure.map π ν := by
    have h := Measure.map_mono hdom hπ
    rw [Measure.map_smul _ hπ.aemeasurable,
      ← Measure.restrict_map hπ hE, boundaryFactor_map_translate ν π hπ heq] at h
    exact h
  have hqdown := boundaryFactor_quasiInvariant ν π hπ heq hq
  have hreal := real_rnDeriv_le_on_set_of_restrict_le
    (Measure.map (fun η : C => g⁻¹ • η) (Measure.map π ν)) (Measure.map π ν)
    hE (Real.exp (R - D)) (Real.exp_nonneg _) hdown
  filter_upwards [hreal, translate_realDensity_pos (Measure.map π ν) hqdown g⁻¹] with η hb hp hη
  have hl := Real.log_le_log hp (hb hη)
  rw [Real.log_exp] at hl
  change D - -Real.log (stationaryRealDensity (Measure.map π ν) g⁻¹ η) ≤ R
  change Real.log (stationaryRealDensity (Measure.map π ν) g⁻¹ η) ≤ R - D at hl
  linarith

end Singularity
