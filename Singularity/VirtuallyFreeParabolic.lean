import Singularity.PowerWordGrowth
import Singularity.ParabolicInfiniteOrder

/-!
# The parabolic obstruction for groups with a finite-index free subgroup

A parabolic has infinite order. The finite-index free-subgroup argument supplies
its linear word growth, removing that hypothesis from the Green/geometric
comparison obstruction. The existence of the finite-index free subgroup for
a general noncocompact finitely generated Fuchsian group remains a separate
geometric/topological obligation. Nonsingularity-to-comparison is also still
required before this yields the full singularity theorem.
-/

noncomputable section
open Set Filter
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- A parabolic in a group with a finite-index free subgroup is undistorted
in the actual finite-support word distance. -/
theorem projective_parabolic_word_growth_of_finiteIndex_free (Γ : Subgroup PSL(2, ℝ))
    (H : Subgroup Γ) [H.FiniteIndex] [IsFreeGroup H]
    (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ))) :
    ∃ κ E : ℝ, 0 < κ ∧ 0 ≤ E ∧ ∀ n : ℕ,
      κ * n - E ≤ (wordDistance s hgen 1 (g ^ n) : ℝ) := by
  apply linear_word_growth_of_finiteIndex_free H s hgen g
  intro hfin
  obtain ⟨n, hn, he⟩ := hfin.exists_pow_eq_one
  exact hpar.not_isOfFinOrder g
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Subtype.val he⟩)

/-- The projective Green comparison is impossible in the presence of a parabolic
and a finite-index free subgroup; no word-growth estimate is assumed. -/
theorem projective_parabolic_green_obstruction_of_finiteIndex_free (Γ : Subgroup PSL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (H : Subgroup Γ) [H.FiniteIndex] [IsFreeGroup H]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ))) (z : ℍ) :
    ¬∃ δ C : ℝ, ∀ x : Γ, |greenDistance s μ 1 x - δ * dist z (x • z)| ≤ C := by
  obtain ⟨κ, E, hκ, _, hword⟩ := projective_parabolic_word_growth_of_finiteIndex_free Γ H s hgen g hpar
  exact projective_parabolic_trace_green_obstruction Γ hne s μ hpos hmass hgen g hpar κ E hκ hword z

/-- The orbit map also fails every positive linear lower bound in word distance. -/
theorem projective_parabolic_no_linear_orbit_lower_bound (Γ : Subgroup PSL(2, ℝ))
    (H : Subgroup Γ) [H.FiniteIndex] [IsFreeGroup H]
    (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g : Γ) (hpar : ProjectiveParabolic (g : PSL(2, ℝ))) (z : ℍ) :
    ¬∃ a C : ℝ, 0 < a ∧ ∀ x : Γ,
      a * (wordDistance s hgen 1 x : ℝ) - C ≤ dist z (x • z) := by
  obtain ⟨κ, E, hκ, _, hword⟩ := projective_parabolic_word_growth_of_finiteIndex_free Γ H s hgen g hpar
  rintro ⟨a, C, ha, hbound⟩
  have hsub : Tendsto (fun n : ℕ => dist z (g ^ n • z) / (n : ℝ)) atTop (𝓝 0) :=
    hpar.displacement_sublinear g z
  apply not_linear_le_sublinear (fun n => dist z (g ^ n • z)) hsub (a * κ) (mul_pos ha hκ) 1 (C + a * E)
  intro n
  have hw := mul_le_mul_of_nonneg_left (hword n) ha.le
  have hb := hbound (g ^ n)
  nlinarith

end Singularity
