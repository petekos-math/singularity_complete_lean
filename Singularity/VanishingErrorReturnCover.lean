import Singularity.RadonNikodymCoboundary

/-!
# Almost-everywhere return covers from vanishing shadow errors

Vanishing error mass excludes eventual membership in the error sets. Thus
an eventual shadow cover, together with vanishing return errors, gives the
finite corrected return cover used in density rigidity. Only the eventual
geometric coverage remains an input here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Singularity

/-- When set masses tend to zero, almost no point belongs to all sufficiently
late sets. Summability and independence are unnecessary. -/
theorem ae_not_eventually_mem_of_measure_tendsto_zero {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (A : ℕ → Set B)
    (hA : Tendsto (fun n => ν (A n)) atTop (𝓝 0)) :
    ∀ᵐ ξ ∂ν, ¬ ∀ᶠ n in atTop, ξ ∈ A n := by
  have hzero (N : ℕ) : ν (⋂ n ≥ N, A n) = 0 := by
    apply le_antisymm ?_ bot_le
    apply ge_of_tendsto hA
    filter_upwards [eventually_ge_atTop N] with n hn
    apply measure_mono
    intro ξ hξ
    exact (mem_iInter.mp (mem_iInter.mp hξ n)) hn
  have he : {ξ | ∀ᶠ n in atTop, ξ ∈ A n} = ⋃ N : ℕ, ⋂ n ≥ N, A n := by
    ext ξ
    simp only [mem_ofPred_eq, eventually_atTop, mem_iUnion, mem_iInter]
  have hu : ν (⋃ N : ℕ, ⋂ n ≥ N, A n) = 0 := measure_iUnion_null hzero
  simpa only [ae_iff, not_not, he] using hu

/-- Eventual membership in shadows forces membership in at least one good
return set when the difference between shadow and return set has vanishing mass. -/
theorem ae_eventual_shadow_has_return {B : Type*} [MeasurableSpace B]
    (ν : Measure B) (T E : ℕ → Set B)
    (herr : Tendsto (fun n => ν (T n \ E n)) atTop (𝓝 0)) :
    ∀ᵐ ξ ∂ν, (∀ᶠ n in atTop, ξ ∈ T n) → ∃ n : ℕ, ξ ∈ T n ∩ E n := by
  filter_upwards [ae_not_eventually_mem_of_measure_tendsto_zero ν (fun n => T n \ E n) herr] with ξ hξ ht
  by_contra hnone
  apply hξ
  filter_upwards [ht] with n hn
  refine ⟨hn, fun hE => hnone ⟨n, hn, hE⟩⟩

/-- Quasi-invariance transfers the preceding return statement through each
correction element. An eventual finite corrected shadow cover becomes a
finite corrected cover by actual good return sets. -/
theorem finite_corrected_return_cover_of_vanishing_error
    {Γ B : Type*} [Group Γ] [Countable Γ] [MeasurableSpace B]
    [MulAction Γ B] [MeasurableConstSMul Γ B]
    (ν : Measure B) (hq : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) ν ≪ ν)
    (T E : ℕ → Set B) (F : Finset Γ)
    (herr : Tendsto (fun n => ν (T n \ E n)) atTop (𝓝 0))
    (hcover : ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∀ᶠ n in atTop, a⁻¹ • ξ ∈ T n) :
    ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ, a⁻¹ • ξ ∈ T n ∩ E n := by
  have hg : ∀ᵐ ξ ∂ν, ∀ a : Γ,
      (∀ᶠ n in atTop, a⁻¹ • ξ ∈ T n) → ∃ n : ℕ, a⁻¹ • ξ ∈ T n ∩ E n := by
    apply ae_all_iff.mpr
    intro a
    exact (show Measure.QuasiMeasurePreserving (fun ξ : B => a⁻¹ • ξ) ν ν from
      ⟨measurable_const_smul a⁻¹, hq a⁻¹⟩).ae (ae_eventual_shadow_has_return ν T E herr)
  filter_upwards [hg, hcover] with ξ hξ hc
  obtain ⟨a, ha, hevent⟩ := hc
  obtain ⟨n, hn⟩ := hξ a hevent
  exact ⟨a, ha, n, hn⟩

end Singularity
