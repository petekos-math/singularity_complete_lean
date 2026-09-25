import Singularity.GreenWordComparison
import Singularity.ParabolicDisplacement

/-!
# The obstruction from linear word growth and sublinear geometric displacement

A Green distance coarsely comparable to word distance cannot differ by a
bounded amount from a sublinear geometric displacement along an undistorted
cyclic subgroup. This proves the quantitative contradiction needed for cusps.
The implication from nonsingularity to a bounded Green/geometric comparison,
and undistortion of parabolics in general Fuchsian groups, are not assumed
silently or proved here: they remain separate obligations.
-/

noncomputable section
open Set Filter
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- A positive linear function cannot be bounded above by a sublinear sequence
plus a constant, even after multiplication by a fixed real number. -/
theorem not_linear_le_sublinear (r : ℕ → ℝ)
    (hr : Tendsto (fun n => r n / (n : ℝ)) atTop (𝓝 0))
    (a : ℝ) (ha : 0 < a) (δ C : ℝ) : ¬∀ n : ℕ, a * n ≤ δ * r n + C := by
  intro h
  have hc : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => δ * (r n / (n : ℝ)) + C / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (hr.const_mul δ).add hc
  have he : ∀ᶠ n : ℕ in atTop, a ≤ δ * (r n / (n : ℝ)) + C / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := (le_div_iff₀ hnp).mpr (h n)
    simpa only [add_div, mul_div_assoc] using hh
  exact ha.not_ge (ge_of_tendsto ht he)

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]

/-- Linear word growth prevents bounded Green/geometric comparison along a
sequence with sublinear geometric displacement. -/
theorem greenDistance_not_roughly_proportional_to_sublinear (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (g : ℕ → Γ) (r : ℕ → ℝ)
    (hr : Tendsto (fun n => r n / (n : ℝ)) atTop (𝓝 0))
    (κ E : ℝ) (hκ : 0 < κ)
    (hword : ∀ n : ℕ, κ * n - E ≤ (wordDistance s hgen 1 (g n) : ℝ)) :
    ¬∃ δ C : ℝ, ∀ n : ℕ, |greenDistance s μ 1 (g n) - δ * r n| ≤ C := by
  obtain ⟨a, b, D, ha, _, _, hcomp⟩ := greenDistance_word_comparison s μ hpos hmass hgen hgap
  rintro ⟨δ, C, hbound⟩
  apply not_linear_le_sublinear r hr (a * κ) (mul_pos ha hκ) δ (C + D + a * E)
  intro n
  have hl := (hcomp 1 (g n)).1
  have hw := mul_le_mul_of_nonneg_left (hword n) ha.le
  have hu := (le_abs_self (greenDistance s μ 1 (g n) - δ * r n)).trans (hbound n)
  nlinarith

/-- A projective conjugate of an upper shear has sublinear displacement. -/
theorem projective_parabolic_displacement_sublinear (g : PSL(2, ℝ))
    (B : SL(2, ℝ)) (u : ℝ) (hg : g = slTwoProjective (B * upperShearMatrix u * B⁻¹)) (z : ℍ) :
    Tendsto (fun n : ℕ => dist z (g ^ n • z) / (n : ℝ)) atTop (𝓝 0) := by
  subst g
  simpa only [← map_pow, slTwoProjective_smul_hyperbolic] using
    conjugate_upperShearMatrix_displacement_sublinear B u z

/-- An undistorted parabolic obstructs bounded comparison for the actual projective Green distance.
The assumed word lower bound is displayed explicitly. -/
theorem projective_parabolic_green_comparison_obstruction (Γ : Subgroup PSL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g : Γ) (B : SL(2, ℝ)) (u : ℝ)
    (hg : (g : PSL(2, ℝ)) = slTwoProjective (B * upperShearMatrix u * B⁻¹))
    (κ E : ℝ) (hκ : 0 < κ)
    (hword : ∀ n : ℕ, κ * n - E ≤ (wordDistance s hgen 1 (g ^ n) : ℝ)) (z : ℍ) :
    ¬∃ δ C : ℝ, ∀ x : Γ, |greenDistance s μ 1 x - δ * dist z (x • z)| ≤ C := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableMul Γ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  have hgap := projectiveNonelementary_rightMarkov_gap Γ hne s μ hpos hmass hgen
  have hsub : Tendsto (fun n : ℕ => dist z (g ^ n • z) / (n : ℝ)) atTop (𝓝 0) :=
    projective_parabolic_displacement_sublinear g B u hg z
  rintro ⟨δ, C, hC⟩
  exact greenDistance_not_roughly_proportional_to_sublinear s μ hpos hmass hgen hgap
    (fun n => g ^ n) (fun n => dist z (g ^ n • z)) hsub κ E hκ hword ⟨δ, C, fun n => hC (g ^ n)⟩

end Singularity
