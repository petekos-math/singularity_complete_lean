import Singularity.FuchsianDeficitCompactness
import Singularity.AbsolutelyContinuousVisualShadows

/-!
# Uniform inverse mass for the canonical mixed shadows

Deficit compactness and absolute continuity imply uniformly almost full
inverse mass for the same countable family used in the covering argument.
Compactness remains an explicit, unproved geometric hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal Topology
namespace Singularity

/-- Uniform exhaustion transfers to any finite measure absolutely continuous
with respect to both the hitting law and visual measure. -/
theorem fuchsianMixedDeficitShadow_uniform_full_mass_of_compactness
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (hcompact : FuchsianDeficitCompactness Γ s μ hpos hmass z)
    (ρ : Measure (OnePoint ℝ)) [IsFiniteMeasure ρ]
    (hρν : ρ ≪ projectiveHittingMeasure Γ s z μ hpos hmass)
    (hρvis : ρ ≪ compactPoissonMeasure z)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ M ≥ N, ∀ g : Γ, ρ
      (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹'
        fuchsianMixedDeficitShadow Γ s μ hpos hmass z M g)ᶜ) < ε := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨δ, hδ, hsmall⟩ := finiteMeasure_uniform_absoluteContinuity ρ
    (projectiveHittingMeasure Γ s z μ hpos hmass) hρν hhalf
  obtain ⟨R, hR⟩ := fuchsianGreenDeficitShadow_uniform_full_mass_of_compactness
    Γ hne s μ hpos hmass hgen z hcompact hδ
  obtain ⟨r, hr, hvisual⟩ := absolutelyContinuous_visualShadow_uniform_full_mass z ρ hρvis hhalf
  obtain ⟨N, hN⟩ := fuchsianMixedDeficitShadow_cofinal Γ s μ hpos hmass z (R : ℝ) hr
  refine ⟨N, fun M hM g => ?_⟩
  have hsub : (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹'
      fuchsianMixedDeficitShadow Γ s μ hpos hmass z M g)ᶜ) ⊆
      (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹'
        fuchsianGreenDeficitShadow Γ s μ hpos hmass z R g)ᶜ) ∪
      (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r)ᶜ) := by
    intro ξ hξ
    by_contra hn
    simp only [mem_union, mem_compl_iff, mem_preimage, not_or, not_not] at hn
    exact hξ (fuchsianMixedDeficitShadow_mono Γ s μ hpos hmass z g hM (hN g hn))
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (hsmall _ (hR g)) (hvisual (g : PSL(2, ℝ)))
    _ = ε := ENNReal.add_halves ε

/-- A positive subprobability reference measure has a uniform positive real
inverse-mass bound for every sufficiently large canonical parameter. -/
theorem fuchsianMixedDeficitShadow_positive_inverse_mass_of_compactness
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (hcompact : FuchsianDeficitCompactness Γ s μ hpos hmass z)
    (ρ : Measure (OnePoint ℝ)) [IsFiniteMeasure ρ]
    (hρν : ρ ≪ projectiveHittingMeasure Γ s z μ hpos hmass)
    (hρvis : ρ ≪ compactPoissonMeasure z)
    (hpositive : 0 < ρ univ) (htotal : ρ univ ≤ 1) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ M ≥ N, ∀ g : Γ,
      ENNReal.ofReal c ≤ ρ ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹'
        fuchsianMixedDeficitShadow Γ s μ hpos hmass z M g) := by
  obtain ⟨N, hN⟩ := fuchsianMixedDeficitShadow_uniform_full_mass_of_compactness
    Γ hne s μ hpos hmass hgen z hcompact ρ hρν hρvis (ENNReal.half_pos hpositive.ne')
  have hhalfle : ρ univ / 2 ≤ 1 := ENNReal.half_le_self.trans htotal
  have hfinite : ρ univ / 2 ≠ ⊤ := ne_top_of_le_ne_top (by simp) hhalfle
  refine ⟨N, (ρ univ / 2).toReal,
    ENNReal.toReal_pos (ENNReal.half_pos hpositive.ne').ne' hfinite, ?_, ?_⟩
  · simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hhalfle
  · intro M hM g
    let T := (fun ξ : OnePoint ℝ => g • ξ) ⁻¹'
      fuchsianMixedDeficitShadow Γ s μ hpos hmass z M g
    have hT : MeasurableSet T :=
      (measurableSet_fuchsianMixedDeficitShadow Γ s μ hpos hmass z M g).preimage
        (measurable_const_smul g)
    rw [ENNReal.ofReal_toReal hfinite]
    calc
      ρ univ / 2 = ρ univ - ρ univ / 2 := (ENNReal.sub_half (measure_ne_top _ _)).symm
      _ ≤ ρ univ - ρ Tᶜ := tsub_le_tsub_left (hN M hM g).le _
      _ = ρ T := by rw [← measure_compl hT.compl (measure_ne_top _ _)]; simp

end Singularity
