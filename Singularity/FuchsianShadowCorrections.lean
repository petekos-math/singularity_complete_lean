import Singularity.FuchsianDensityCocycle

/-!
# Uniform bounds for finitely many correction elements

The finite-correction hypothesis in the return-cover density upgrade follows
from the proved word bound for the hitting cocycle and the geometric bound
for the visual cocycle. No global bound on the density is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- Under nonsingularity, any finite list of correction elements has a common
bound for the difference of the actual hitting and visual cocycles. -/
theorem fuchsian_finite_cocycle_difference_bound
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (hns : ¬ projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z)
    (F : Finset Γ) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
      ∀ a ∈ F, |stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) a ξ -
        stationaryLogCocycle (compactPoissonMeasure z) a ξ| ≤ J := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let ν := projectiveHittingMeasure Γ s z μ hpos hmass
  have hac := fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular Γ hne s μ hpos hmass hgen z hns
  obtain ⟨b, hb, hwalk⟩ := fuchsian_logCocycle_word_bound Γ hne s μ hpos hmass hgen z
  have hvis : ∀ᵐ ξ ∂ν, ∀ a : Γ,
      |stationaryLogCocycle (compactPoissonMeasure z) a ξ| ≤ dist z (a • z) := by
    apply ae_all_iff.mpr
    intro a
    exact hac.ae_le (projective_visual_logCocycle_bound z (a : PSL(2, ℝ)))
  let c : Γ → ℝ := fun a => b * (wordDistance s hgen 1 a : ℝ) + dist z (a • z)
  have hc : ∀ a, 0 ≤ c a := by
    intro a
    dsimp [c]
    positivity
  refine ⟨∑ a ∈ F, c a, Finset.sum_nonneg (fun a _ => hc a), ?_⟩
  filter_upwards [hwalk, hvis] with ξ hw hv
  intro a ha
  calc
    _ ≤ |stationaryLogCocycle ν a ξ| + |stationaryLogCocycle (compactPoissonMeasure z) a ξ| := abs_sub _ _
    _ ≤ c a := add_le_add (hw a) (hv a)
    _ ≤ ∑ a ∈ F, c a := Finset.single_le_sum (fun a _ => hc a) ha

end Singularity
