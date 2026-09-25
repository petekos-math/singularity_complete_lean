import Singularity.GreenDistance
import Singularity.WordDistance
import Singularity.ProjectiveNonelementaryDynamics

/-!
# Green distance is coarsely equivalent to the symmetric word distance

Finite semigroup generation replaces inverse generators by uniformly bounded
forward words. Combining this with the spectral Green bounds gives linear
comparison with the actual symmetric word distance. For nonelementary
projective groups, the spectral-gap hypothesis is discharged internally.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]

/-- Uniform linear Green bounds for the symmetric word distance of the support. -/
theorem greenDistance_word_comparison (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ a b D : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ D ∧ ∀ x y,
      a * (wordDistance s hgen x y : ℝ) - D ≤ greenDistance s μ x y ∧
        greenDistance s μ x y ≤ b * (wordDistance s hgen x y : ℝ) := by
  obtain ⟨a, b, D, ha, hb, hD, hcomp⟩ := greenDistance_jump_comparison s μ hpos hmass hgen hgap
  obtain ⟨L, hL, hlen⟩ := jumpDistance_le_wordDistance_mul s hgen
  refine ⟨a, b * L, D, ha, mul_pos hb (by exact_mod_cast hL), hD, fun x y => ?_⟩
  obtain ⟨hl, hu⟩ := hcomp x y
  have hshort : (wordDistance s hgen x y : ℝ) ≤ (jumpDistance s hgen x y : ℝ) := by
    exact_mod_cast wordDistance_le_jumpDistance s hgen x y
  have hlong : (jumpDistance s hgen x y : ℝ) ≤ (L : ℝ) * (wordDistance s hgen x y : ℝ) := by
    exact_mod_cast hlen x y
  constructor
  · exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hshort ha.le) D).trans hl
  · exact hu.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlong hb.le)

/-- The Green/word comparison for the original projective walk requires no assumed spectral gap. -/
theorem projectiveNonelementary_greenDistance_word_comparison (Γ : Subgroup PSL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    ∃ a b D : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ D ∧ ∀ x y,
      a * (wordDistance s hgen x y : ℝ) - D ≤ greenDistance s μ x y ∧
        greenDistance s μ x y ≤ b * (wordDistance s hgen x y : ℝ) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableMul Γ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  exact greenDistance_word_comparison s μ hpos hmass hgen
    (projectiveNonelementary_rightMarkov_gap Γ hne s μ hpos hmass hgen)

end Singularity
