import Singularity.GreenPositive

/-!
# Harnack inequalities from permitted finite paths

Appending any continuation to a fixed path bounds the Green function from below.
We prove the inequality directly from the already checked first-step equation,
then derive a comparison constant independent of the target state.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hμ hgap in
/-- Taking a specified first jump gives a lower bound for the Green function. -/
theorem walkGreen_jump_le (x y : Γ) {g : Γ} (hg : g ∈ s) :
    μ g * walkGreen s μ (x * g) y ≤ walkGreen s μ x y := by
  have hs : μ g * walkGreen s μ (x * g) y ≤
      ∑ a ∈ s, μ a * walkGreen s μ (x * a) y :=
    Finset.single_le_sum (fun a ha => mul_nonneg (hμ a ha) (walkGreen_nonneg s μ hμ _ _)) hg
  have he := walkGreen_first_step s μ hgap x y
  have hδ : 0 ≤ (if x = y then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  linarith

include hμ hgap in
/-- Following a fixed word and then any continuation gives the path Harnack inequality. -/
theorem walkGreen_word_le (n : ℕ) (w : WalkWord s n) (x y : Γ) :
    walkWeight s μ n w * walkGreen s μ (walkEndpoint s n x w) y ≤ walkGreen s μ x y := by
  induction n generalizing x with
  | zero => simp only [walkWeight, walkEndpoint, one_mul, le_refl]
  | succ n ih =>
    change (μ w.1 * walkWeight s μ n w.2) *
      walkGreen s μ (walkEndpoint s n (x * w.1) w.2) y ≤ walkGreen s μ x y
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left (ih w.2 (x * w.1)) (hμ w.1 w.1.property)).trans
      (walkGreen_jump_le s μ hμ hgap x y w.1.property)

include hgap in
/-- Irreducibility gives comparison of Green rows uniformly in the target. -/
theorem exists_greenHarnackConstant (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x z : Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, walkGreen s μ z y ≤ C * walkGreen s μ x y := by
  obtain ⟨n, w, hw⟩ := exists_walkWord_between s hgen x z
  have hp := walkWeight_pos s μ hpos n w
  refine ⟨(walkWeight s μ n w)⁻¹, inv_pos.mpr hp, ?_⟩
  intro y
  have h := walkGreen_word_le s μ (fun g hg => (hpos g hg).le) hgap n w x y
  rw [hw] at h
  have hd : walkGreen s μ z y ≤ walkGreen s μ x y / walkWeight s μ n w :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using h)
  simpa only [div_eq_mul_inv, mul_comm] using hd

end Singularity
