import Singularity.StationaryLogCocycle

/-!
# Changing the reference measure changes the logarithmic cocycle by a coboundary

Absolute continuity is enough: the density need not be bounded or positive on
the whole reference space. Positivity is used only almost everywhere for the
absolutely continuous measure itself. The action preserves both measure classes.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical

namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B]

/-- Quasi-invariance for all elements also gives the reverse absolute continuity. -/
theorem translate_reverse_absolutelyContinuous (ν : Measure B)
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν) (g : Γ) :
    ν ≪ Measure.map (fun ξ : B => g • ξ) ν := by
  have h := (hq g⁻¹).map (measurable_const_smul g)
  rw [Measure.map_map (measurable_const_smul g) (measurable_const_smul g⁻¹)] at h
  have he : (fun ξ : B => g • ξ) ∘ (fun ξ : B => g⁻¹ • ξ) = id := by
    funext ξ
    exact smul_inv_smul g ξ
  simpa only [he, Measure.map_id] using h

/-- Actual translated Radon–Nikodym derivatives are positive and finite for any
finite quasi-invariant measure; stationarity is unnecessary for this statement. -/
theorem translate_realDensity_pos (ν : Measure B) [IsFiniteMeasure ν]
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν) (g : Γ) :
    ∀ᵐ ξ ∂ν, 0 < stationaryRealDensity ν g ξ := by
  filter_upwards [Measure.rnDeriv_pos' (translate_reverse_absolutelyContinuous ν hq g),
    Measure.rnDeriv_lt_top (Measure.map (fun ξ : B => g • ξ) ν) ν] with ξ hp hf
  exact ENNReal.toReal_pos hp.ne' hf.ne

/-- The exact multiplicative change-of-measure identity for translated densities. -/
theorem translated_density_coboundary (ν m : Measure B) [IsFiniteMeasure ν] [IsFiniteMeasure m]
    (hac : ν ≪ m)
    (hν : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)
    (hm : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) m ≪ m) (g : Γ) :
    ∀ᵐ ξ ∂m, stationaryRealDensity ν g ξ * (ν.rnDeriv m ξ).toReal =
      (ν.rnDeriv m (g⁻¹ • ξ)).toReal * stationaryRealDensity m g ξ := by
  have hmap := (measurableEmbedding_const_smul (α := B) g).rnDeriv_map ν m
  have hq : Measure.QuasiMeasurePreserving (fun ξ : B => g⁻¹ • ξ) m m :=
    ⟨measurable_const_smul g⁻¹, hm g⁻¹⟩
  have hleft := Measure.rnDeriv_mul_rnDeriv (κ := m) (hν g)
  have hright := Measure.rnDeriv_mul_rnDeriv (κ := m) (hac.map (measurable_const_smul g))
  filter_upwards [hq.ae hmap, hleft, hright] with ξ he hl hr
  simp only [smul_inv_smul] at he
  simp only [Pi.mul_apply] at hl hr
  rw [he] at hr
  have h := congrArg ENNReal.toReal (hl.trans hr.symm)
  simpa only [ENNReal.toReal_mul, stationaryRealDensity, stationaryDensity] using h

/-- The logarithmic cocycles of absolutely continuous quasi-invariant finite
measures differ by the logarithm of their actual density. -/
theorem stationaryLogCocycle_change_measure (ν m : Measure B)
    [IsFiniteMeasure ν] [IsFiniteMeasure m] (hac : ν ≪ m)
    (hν : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)
    (hm : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) m ≪ m) (g : Γ) :
    ∀ᵐ ξ ∂ν, stationaryLogCocycle ν g ξ = stationaryLogCocycle m g ξ +
      Real.log ((ν.rnDeriv m ξ).toReal) - Real.log ((ν.rnDeriv m (g • ξ)).toReal) := by
  have hp : ∀ᵐ ξ ∂ν, 0 < (ν.rnDeriv m ξ).toReal := by
    filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le (Measure.rnDeriv_lt_top ν m)] with ξ hp hf
    exact ENNReal.toReal_pos hp.ne' hf.ne
  have hq : Measure.QuasiMeasurePreserving (fun ξ : B => g • ξ) ν ν :=
    ⟨measurable_const_smul g, hν g⟩
  filter_upwards [hac.ae_le (translated_density_coboundary ν m hac hν hm g⁻¹), hp, hq.ae hp,
    translate_realDensity_pos ν hν g⁻¹,
    hac.ae_le (translate_realDensity_pos m hm g⁻¹)] with ξ he hp hpg hK hKm
  simp only [inv_inv] at he
  have hlog := congrArg Real.log he
  rw [Real.log_mul hK.ne' hp.ne', Real.log_mul hpg.ne' hKm.ne'] at hlog
  dsimp [stationaryLogCocycle]
  linarith

end Singularity
