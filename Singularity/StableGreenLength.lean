import Singularity.GreenWordComparison
import Mathlib.Analysis.Subadditive

/-!
# Stable translation length for the asymmetric Green distance

Fekete's lemma supplies an actual limit along powers. Positivity follows from
linear word growth and the Green/word comparison. No symmetry is used.
-/

noncomputable section
open Set Filter
open scoped Classical Topology

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Stable Green length, expressed as the infimum of positive-exponent ratios. -/
def stableGreenLength (s : Finset Γ) (μ : Γ → ℝ) (g : Γ) : ℝ :=
  sInf ((fun n : ℕ => greenDistance s μ 1 (g ^ n) / n) '' Ici 1)

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hmass hgen hgap in
/-- Distances along powers form a subadditive sequence. -/
theorem greenDistance_powers_subadditive (g : Γ) :
    Subadditive (fun n : ℕ => greenDistance s μ 1 (g ^ n)) := by
  intro m n
  dsimp only
  rw [pow_add]
  have ht := greenDistance_triangle s μ hpos hmass hgen hgap 1 (g ^ m) (g ^ m * g ^ n)
  have hl : greenDistance s μ (g ^ m) (g ^ m * g ^ n) = greenDistance s μ 1 (g ^ n) := by
    simpa only [mul_one] using greenDistance_left s μ (g ^ m) 1 (g ^ n)
  rwa [hl] at ht

include hpos hmass hgen hgap in
/-- All normalized power distances have the common lower bound zero. -/
theorem greenDistance_power_ratios_bddBelow (g : Γ) :
    BddBelow (range (fun n : ℕ => greenDistance s μ 1 (g ^ n) / n)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (greenDistance_nonneg s μ hpos hmass hgen hgap 1 (g ^ n)) (Nat.cast_nonneg n)

include hpos hmass hgen hgap in
/-- The defining infimum is the asymptotic Green translation length. -/
theorem greenDistance_powers_tendsto (g : Γ) :
    Tendsto (fun n : ℕ => greenDistance s μ 1 (g ^ n) / n) atTop
      (𝓝 (stableGreenLength s μ g)) := by
  have ht := (greenDistance_powers_subadditive s μ hpos hmass hgen hgap g).tendsto_lim
    (greenDistance_power_ratios_bddBelow s μ hpos hmass hgen hgap g)
  simpa only [Subadditive.lim, stableGreenLength] using ht

include hpos hmass hgen hgap in
/-- Stable Green length is nonnegative. -/
theorem stableGreenLength_nonneg (g : Γ) : 0 ≤ stableGreenLength s μ g := by
  apply ge_of_tendsto (greenDistance_powers_tendsto s μ hpos hmass hgen hgap g)
  exact Filter.Eventually.of_forall fun n =>
    div_nonneg (greenDistance_nonneg s μ hpos hmass hgen hgap 1 (g ^ n)) (Nat.cast_nonneg n)

include hpos hmass hgen hgap in
/-- Each positive power gives an upper bound on stable length. -/
theorem stableGreenLength_le_ratio (g : Γ) (n : ℕ) (hn : n ≠ 0) :
    stableGreenLength s μ g ≤ greenDistance s μ 1 (g ^ n) / n := by
  have ht := (greenDistance_powers_subadditive s μ hpos hmass hgen hgap g).lim_le_div
    (greenDistance_power_ratios_bddBelow s μ hpos hmass hgen hgap g) hn
  simpa only [Subadditive.lim, stableGreenLength] using ht

include hpos hmass hgen hgap in
/-- A linear word lower bound forces strictly positive stable Green length. -/
theorem stableGreenLength_pos_of_word_growth (g : Γ) (κ E : ℝ) (hκ : 0 < κ)
    (hword : ∀ n : ℕ, κ * n - E ≤ (wordDistance s hgen 1 (g ^ n) : ℝ)) :
    0 < stableGreenLength s μ g := by
  obtain ⟨a, b, D, ha, _, _, hcomp⟩ := greenDistance_word_comparison s μ hpos hmass hgen hgap
  have hc : Tendsto (fun n : ℕ => (a * E + D) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => a * κ - (a * E + D) / (n : ℝ)) atTop (𝓝 (a * κ)) := by
    simpa using tendsto_const_nhds.sub hc
  have hb : a * κ ≤ stableGreenLength s μ g := by
    apply le_of_tendsto_of_tendsto ht (greenDistance_powers_tendsto s μ hpos hmass hgen hgap g)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have hw := mul_le_mul_of_nonneg_left (hword n) ha.le
    have hg := (hcomp 1 (g ^ n)).1
    apply (le_div_iff₀ hnp).mpr
    have he : (a * κ - (a * E + D) / (n : ℝ)) * n = a * κ * n - (a * E + D) := by
      field_simp
    rw [he]
    nlinarith
  exact (mul_pos ha hκ).trans_le hb

include hpos hmass hgen hgap in
/-- Every finite-order element has zero stable Green length. -/
theorem stableGreenLength_eq_zero_of_isOfFinOrder (g : Γ) (hg : IsOfFinOrder g) :
    stableGreenLength s μ g = 0 := by
  obtain ⟨n, hn, he⟩ := hg.exists_pow_eq_one
  apply le_antisymm _ (stableGreenLength_nonneg s μ hpos hmass hgen hgap g)
  have hl := stableGreenLength_le_ratio s μ hpos hmass hgen hgap g n hn.ne'
  simpa only [he, greenDistance_self s μ hpos hgap 1, zero_div] using hl

include hpos hmass hgen hgap in
/-- Stable Green length is homogeneous under nonnegative integral powers. -/
theorem stableGreenLength_pow (g : Γ) (m : ℕ) :
    stableGreenLength s μ (g ^ m) = m * stableGreenLength s μ g := by
  by_cases hm : m = 0
  · subst m
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact stableGreenLength_eq_zero_of_isOfFinOrder s μ hpos hmass hgen hgap 1
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by decide, one_pow 1⟩)
  have hmp : 0 < m := Nat.pos_of_ne_zero hm
  have ht : Tendsto (fun n : ℕ => m * n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => hn.trans (by nlinarith)⟩
  have hl := ((greenDistance_powers_tendsto s μ hpos hmass hgen hgap g).comp ht).const_mul (m : ℝ)
  have he : (fun n : ℕ => (m : ℝ) * (greenDistance s μ 1 (g ^ (m * n)) / (m * n : ℕ))) =
      (fun n : ℕ => greenDistance s μ 1 ((g ^ m) ^ n) / n) := by
    funext n
    rw [pow_mul, Nat.cast_mul]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp
  change Tendsto (fun n : ℕ => (m : ℝ) * (greenDistance s μ 1 (g ^ (m * n)) / (m * n : ℕ)))
    atTop (𝓝 ((m : ℝ) * stableGreenLength s μ g)) at hl
  rw [he] at hl
  exact tendsto_nhds_unique (greenDistance_powers_tendsto s μ hpos hmass hgen hgap (g ^ m)) hl

end Singularity
