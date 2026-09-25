import Singularity.StationaryLogCocycle
import Singularity.InvariantConullSet

/-!
# An invariant full-measure domain for the stationary cocycle

All group identities and Green bounds hold pointwise on a single measurable
invariant conull subset. The original Radon–Nikodym representatives are used
without asserting identities on their exceptional null sets.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical

namespace Singularity

/-- All logarithmic cocycle identities and Green bounds hold simultaneously
on an exactly invariant measurable conull set. -/
theorem stationaryLogCocycle_invariant_domain
    {Γ B : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (ν : Measure B) [IsFiniteMeasure ν]
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν) :
    ∃ E : Set B, MeasurableSet E ∧ (∀ᵐ ξ ∂ν, ξ ∈ E) ∧
      (∀ g : Γ, (fun ξ : B => g • ξ) ⁻¹' E = E) ∧
      ∀ ξ ∈ E, stationaryLogCocycle ν (1 : Γ) ξ = 0 ∧
        (∀ g h : Γ, stationaryLogCocycle ν (g * h) ξ =
          stationaryLogCocycle ν g (h • ξ) + stationaryLogCocycle ν h ξ) ∧
        (∀ g : Γ, -greenDistance s μ g 1 ≤ stationaryLogCocycle ν g ξ ∧
          stationaryLogCocycle ν g ξ ≤ greenDistance s μ 1 g) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let P := fun ξ : B => stationaryLogCocycle ν (1 : Γ) ξ = 0 ∧
    (∀ g h : Γ, stationaryLogCocycle ν (g * h) ξ =
      stationaryLogCocycle ν g (h • ξ) + stationaryLogCocycle ν h ξ) ∧
    (∀ g : Γ, -greenDistance s μ g 1 ≤ stationaryLogCocycle ν g ξ ∧
      stationaryLogCocycle ν g ξ ≤ greenDistance s μ 1 g)
  have hm : MeasurableSet {ξ | P ξ} := by
    apply MeasurableSet.inter (measurableSet_eq_fun (measurable_stationaryLogCocycle ν 1) measurable_const)
    apply MeasurableSet.inter
    · have hm := MeasurableSet.iInter (fun g : Γ => MeasurableSet.iInter (fun h : Γ =>
        measurableSet_eq_fun (measurable_stationaryLogCocycle ν (g * h))
          (((measurable_stationaryLogCocycle ν g).comp (measurable_const_smul h)).add
            (measurable_stationaryLogCocycle ν h))))
      convert hm using 1
      apply iff_of_eq
      congr 1
      ext ξ
      simp only [mem_iInter, mem_ofPred_eq, Function.comp_apply, Pi.add_apply]
      rfl
    · have hm := MeasurableSet.iInter (fun g : Γ =>
        (measurableSet_le (measurable_const : Measurable (fun _ : B => -greenDistance s μ g 1))
          (measurable_stationaryLogCocycle ν g)).inter
        (measurableSet_le (measurable_stationaryLogCocycle ν g)
          (measurable_const : Measurable (fun _ : B => greenDistance s μ 1 g))))
      convert hm using 1
      apply iff_of_eq
      congr 1
      ext ξ
      simp only [mem_iInter, mem_inter_iff, mem_ofPred_eq]
      rfl
  have hc : ∀ᵐ ξ ∂ν, ∀ g h : Γ, stationaryLogCocycle ν (g * h) ξ =
      stationaryLogCocycle ν g (h • ξ) + stationaryLogCocycle ν h ξ :=
    ae_all_iff.mpr (fun g => ae_all_iff.mpr (stationaryLogCocycle_mul s μ hpos hgen ν hstat g))
  have hall : ∀ᵐ ξ ∂ν, P ξ := by
    filter_upwards [stationaryLogCocycle_one (Γ := Γ) ν, hc,
      stationaryLogCocycle_ae_green_bounds s μ hpos hgen ν hstat hmass hgap] with ξ h1 hc hb
    exact ⟨h1, hc, hb⟩
  obtain ⟨E, hE, hfull, hsub, hinv⟩ := exists_invariant_conull_subset ν
    (fun g => (stationary_translate_equivalent s μ hpos hgen ν hstat g).1) hm hall
  exact ⟨E, hE, hfull, hinv, fun ξ hξ => hsub hξ⟩

end Singularity
