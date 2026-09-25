import Singularity.GreenJumpBounds
import Singularity.GreenProductBounds
import Singularity.ReflectedSupport

/-!
# Green distance and its coarse comparison with permitted word length

The Green distance is minus the logarithm of the normalized Green kernel.
For nonsymmetric walks it is a directed distance; no symmetric metric instance
is claimed. The checked exponential bounds give uniform linear upper and lower
bounds in shortest jump length, with an additive constant in the lower bound.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The possibly asymmetric Green distance of the actual random walk. -/
def greenDistance (s : Finset Γ) (μ : Γ → ℝ) (x y : Γ) : ℝ :=
  -Real.log (walkGreen s μ x y / walkGreen s μ 1 1)

/-- All diagonal Green entries have the same value. -/
theorem walkGreen_diagonal_eq (s : Finset Γ) (μ : Γ → ℝ) (x : Γ) :
    walkGreen s μ x x = walkGreen s μ 1 1 := by
  simpa only [mul_one] using walkGreen_left s μ x 1 1

/-- The Green distance is left invariant. -/
theorem greenDistance_left (s : Finset Γ) (μ : Γ → ℝ) (g x y : Γ) :
    greenDistance s μ (g * x) (g * y) = greenDistance s μ x y := by
  simp only [greenDistance, walkGreen_left]

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hgap in
/-- The distance from a vertex to itself is zero. -/
theorem greenDistance_self (x : Γ) : greenDistance s μ x x = 0 := by
  have hG := zero_lt_one.trans_le (walkGreen_diag_ge_one s μ (fun g hg => (hpos g hg).le) hgap 1)
  simp [greenDistance, walkGreen_diagonal_eq, hG.ne']

include hpos hmass hgen hgap in
/-- Normalizing by the diagonal gives a number at most one. -/
theorem normalizedGreen_le_one (x y : Γ) : walkGreen s μ x y / walkGreen s μ 1 1 ≤ 1 := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have h := walkGreen_superharmonic_bound s μ (fun g hg => (hpos g hg).le) hmass hgap
    (fun _ => 1) (fun _ => zero_le_one) (fun _ => by simpa using hmass.le) x y
  rw [walkGreen_diagonal_eq] at h
  have hG := zero_lt_one.trans_le (walkGreen_diag_ge_one s μ (fun g hg => (hpos g hg).le) hgap 1)
  apply (div_le_one hG).mpr
  simpa only [mul_one] using h

include hpos hmass hgen hgap in
/-- Green distance is nonnegative. -/
theorem greenDistance_nonneg (x y : Γ) : 0 ≤ greenDistance s μ x y := by
  apply neg_nonneg.mpr
  exact Real.log_nonpos (div_nonneg (walkGreen_nonneg s μ (fun g hg => (hpos g hg).le) x y)
    (walkGreen_nonneg s μ (fun g hg => (hpos g hg).le) 1 1))
    (normalizedGreen_le_one s μ hpos hmass hgen hgap x y)

include hpos hmass hgen hgap in
/-- The directed triangle inequality follows from the Green product inequality. -/
theorem greenDistance_triangle (x u y : Γ) :
    greenDistance s μ x y ≤ greenDistance s μ x u + greenDistance s μ u y := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hG := walkGreen_pos s μ hpos hgen hgap 1 1
  have hxu := div_pos (walkGreen_pos s μ hpos hgen hgap x u) hG
  have huy := div_pos (walkGreen_pos s μ hpos hgen hgap u y) hG
  have hprod := walkGreen_product_le s μ (fun g hg => (hpos g hg).le) hmass hgap x u y
  rw [walkGreen_diagonal_eq] at hprod
  have hnorm : (walkGreen s μ x u / walkGreen s μ 1 1) *
      (walkGreen s μ u y / walkGreen s μ 1 1) ≤ walkGreen s μ x y / walkGreen s μ 1 1 := by
    rw [div_mul_div_comm]
    apply (div_le_div_iff₀ (mul_pos hG hG) hG).mpr
    nlinarith [mul_le_mul_of_nonneg_left hprod hG.le]
  have hlog := Real.log_le_log (mul_pos hxu huy) hnorm
  rw [Real.log_mul hxu.ne' huy.ne'] at hlog
  dsimp [greenDistance]
  linarith

include hpos hmass hgen hgap in
/-- Green distance is bounded above and below linearly in minimum permitted word length. -/
theorem greenDistance_jump_comparison :
    ∃ a b D : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ D ∧ ∀ x y,
      a * (jumpDistance s hgen x y : ℝ) - D ≤ greenDistance s μ x y ∧
        greenDistance s μ x y ≤ b * (jumpDistance s hgen x y : ℝ) := by
  obtain ⟨A, p, q, hA, hp, hp1, hq, hq1, hb⟩ :=
    normalizedGreen_exponential_jump_bounds s μ hpos hmass hgen hgap
  refine ⟨-Real.log q, -Real.log p, |Real.log A|,
    neg_pos.mpr (Real.log_neg hq hq1), neg_pos.mpr (Real.log_neg hp hp1), abs_nonneg _, fun x y => ?_⟩
  obtain ⟨hl, hu⟩ := hb x y
  have hG := div_pos (walkGreen_pos s μ hpos hgen hgap x y)
    (walkGreen_pos s μ hpos hgen hgap 1 1)
  have hlogl := Real.log_le_log (pow_pos hp _) hl
  have hlogu := Real.log_le_log hG hu
  rw [Real.log_pow] at hlogl
  rw [Real.log_mul hA.ne' (pow_pos hq _).ne', Real.log_pow] at hlogu
  dsimp [greenDistance]
  constructor <;> nlinarith [le_abs_self (Real.log A)]

end Singularity
