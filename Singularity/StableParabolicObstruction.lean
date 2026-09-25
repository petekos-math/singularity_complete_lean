import Singularity.StableGreenLength
import Singularity.VirtuallyFreeParabolic

/-!
# Positive stable Green length and the parabolic length obstruction

Every infinite-order element of a group with a finite-index free subgroup
has positive stable Green length. For parabolic elements the hyperbolic
translation length is zero, so the discrepancy grows linearly even if only
sublinear, rather than bounded, error is requested.

These statements do not infer singularity from nonsingularity rigidity. That
implication and the Fuchsian finite-index free-subgroup theorem remain unproved.
-/

noncomputable section
open Set Filter
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G]

/-- Infinite-order elements have positive stable Green length in the virtually free case. -/
theorem stableGreenLength_pos_of_finiteIndex_free (H : Subgroup G) [H.FiniteIndex] [IsFreeGroup H]
    (s : Finset G) (μ : G → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set G) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (g : G) (hg : ¬IsOfFinOrder g) :
    0 < stableGreenLength s μ g := by
  obtain ⟨κ, E, hκ, _, hw⟩ := linear_word_growth_of_finiteIndex_free H s hgen g hg
  exact stableGreenLength_pos_of_word_growth s μ hpos hmass hgen hgap g κ E hκ hw

/-- In this setting stable Green length vanishes exactly on finite-order elements. -/
theorem stableGreenLength_eq_zero_iff_of_finiteIndex_free (H : Subgroup G)
    [H.FiniteIndex] [IsFreeGroup H]
    (s : Finset G) (μ : G → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set G) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (g : G) :
    stableGreenLength s μ g = 0 ↔ IsOfFinOrder g := by
  constructor
  · intro hz
    by_contra hfin
    exact (stableGreenLength_pos_of_finiteIndex_free H s μ hpos hmass hgen hgap g hfin).ne' hz
  · exact stableGreenLength_eq_zero_of_isOfFinOrder s μ hpos hmass hgen hgap g

/-- Along any parabolic, the normalized discrepancy tends to a strictly positive limit.
The scaling factor is arbitrary, and no additive comparison hypothesis is needed. -/
theorem projective_parabolic_green_discrepancy_tendsto (Γ : Subgroup PSL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (H : Subgroup Γ) [H.FiniteIndex] [IsFreeGroup H]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ))) (z : ℍ) (δ : ℝ) :
    0 < stableGreenLength s μ g ∧
      Tendsto (fun n : ℕ => (greenDistance s μ 1 (g ^ n) - δ * dist z (g ^ n • z)) / n)
        atTop (𝓝 (stableGreenLength s μ g)) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableMul Γ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  have hgap := projectiveNonelementary_rightMarkov_gap Γ hne s μ hpos hmass hgen
  obtain ⟨κ, E, hκ, _, hw⟩ := projective_parabolic_word_growth_of_finiteIndex_free Γ H s hgen g hpar
  refine ⟨stableGreenLength_pos_of_word_growth s μ hpos hmass hgen hgap g κ E hκ hw, ?_⟩
  have hsub : Tendsto (fun n : ℕ => dist z (g ^ n • z) / (n : ℝ)) atTop (𝓝 0) :=
    hpar.displacement_sublinear g z
  have ht := (greenDistance_powers_tendsto s μ hpos hmass hgen hgap g).sub
    (hsub.const_mul δ)
  simpa only [sub_div, mul_div_assoc, mul_zero, sub_zero] using ht

/-- Even sublinear Green/hyperbolic discrepancy is impossible along a parabolic. -/
theorem projective_parabolic_no_sublinear_green_discrepancy (Γ : Subgroup PSL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (H : Subgroup Γ) [H.FiniteIndex] [IsFreeGroup H]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ))) (z : ℍ) :
    ¬∃ δ : ℝ, Tendsto
      (fun n : ℕ => (greenDistance s μ 1 (g ^ n) - δ * dist z (g ^ n • z)) / n) atTop (𝓝 0) := by
  rintro ⟨δ, hδ⟩
  obtain ⟨hp, ht⟩ := projective_parabolic_green_discrepancy_tendsto Γ H hne s μ hpos hmass hgen g hpar z δ
  exact hp.ne' (tendsto_nhds_unique ht hδ)

end Singularity
