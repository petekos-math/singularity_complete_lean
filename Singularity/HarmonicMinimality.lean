import Singularity.EventualOscillation
import Singularity.GreenFirstHit

/-!
# Minimality from a uniform Green lower comparison

The substantive hypothesis is a positive lower bound for the probability of
visiting a sequence under the H-transform. Its starting index may depend on x.
This file proves the harmonic-cone implication, not that geometric rays satisfy
the hypothesis.
-/

noncomputable section
open Set Filter
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- A uniform H-transform hitting lower bound compares every nonnegative
superharmonic function to H along the same sequence. -/
theorem eventual_superharmonic_ratio_comparison (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (H : Γ → ℝ) (hH : ∀ x, 0 < H x) (y : ℕ → Γ) (c : ℝ)
    (hminor : ∀ x, ∀ᶠ n in atTop,
      c * walkGreen s μ (y n) (y n) * H x ≤ walkGreen s μ x (y n) * H (y n))
    (f : Γ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hh : ∀ x, ∑ g ∈ s, μ g * f (x * g) ≤ f x) (x : Γ) :
    ∀ᶠ n in atTop, c * (f (y n) / H (y n)) ≤ f x / H x := by
  filter_upwards [hminor x] with n hn
  have hg := walkGreen_superharmonic_bound s μ hμ hmass hgap f hf hh x (y n)
  have hd : 0 < walkGreen s μ (y n) (y n) :=
    lt_of_lt_of_le zero_lt_one (walkGreen_diag_ge_one s μ hμ hgap (y n))
  have h₁ := mul_le_mul_of_nonneg_right hn (hf (y n))
  have h₂ := mul_le_mul_of_nonneg_right hg (hH (y n)).le
  have hcancel : walkGreen s μ (y n) (y n) * (c * f (y n) * H x) ≤
      walkGreen s μ (y n) (y n) * (f x * H (y n)) := by nlinarith
  have hfinal := (mul_le_mul_iff_right₀ hd).mp hcancel
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ (hH (y n)) (hH x)).mpr hfinal

/-- Every harmonic function between zero and H is a scalar multiple of H,
provided one sequence has a uniform positive H-transform hitting lower bound. -/
theorem harmonic_minimal_of_green_minorization (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (H : Γ → ℝ) (hH : ∀ x, 0 < H x)
    (hHharm : ∀ x, ∑ g ∈ s, μ g * H (x * g) = H x)
    (y : ℕ → Γ) (c : ℝ) (hc : 0 < c)
    (hminor : ∀ x, ∀ᶠ n in atTop,
      c * walkGreen s μ (y n) (y n) * H x ≤ walkGreen s μ x (y n) * H (y n))
    (f : Γ → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ H x)
    (hfharm : ∀ x, ∑ g ∈ s, μ g * f (x * g) = f x) :
    ∃ a ∈ Icc (0 : ℝ) 1, ∀ x, f x = a * H x := by
  let r : Γ → ℝ := fun x => f x / H x
  have hr (x : Γ) : r x ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (hf x).1 (hH x).le, (div_le_one (hH x)).mpr (hf x).2⟩
  have hbelow : BddBelow (range r) := ⟨0, by rintro _ ⟨x, rfl⟩; exact (hr x).1⟩
  have habove : BddAbove (range r) := ⟨1, by rintro _ ⟨x, rfl⟩; exact (hr x).2⟩
  let m := sInf (range r)
  let M := sSup (range r)
  have hlo (x : Γ) : m ≤ r x := csInf_le hbelow (mem_range_self x)
  have hhi (x : Γ) : r x ≤ M := le_csSup habove (mem_range_self x)
  have hlowpos (x : Γ) : 0 ≤ f x - m * H x := by
    have hh := (le_div_iff₀ (hH x)).mp (hlo x)
    linarith
  have huppos (x : Γ) : 0 ≤ M * H x - f x := by
    have hh := (div_le_iff₀ (hH x)).mp (hhi x)
    linarith
  have hlowharm (x : Γ) :
      ∑ g ∈ s, μ g * (f (x * g) - m * H (x * g)) ≤ f x - m * H x := by
    have he : ∑ g ∈ s, μ g * (f (x * g) - m * H (x * g)) =
        (∑ g ∈ s, μ g * f (x * g)) - m * (∑ g ∈ s, μ g * H (x * g)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_left_comm]
    rw [he, hfharm x, hHharm x]
  have huppharm (x : Γ) :
      ∑ g ∈ s, μ g * (M * H (x * g) - f (x * g)) ≤ M * H x - f x := by
    have he : ∑ g ∈ s, μ g * (M * H (x * g) - f (x * g)) =
        M * (∑ g ∈ s, μ g * H (x * g)) - (∑ g ∈ s, μ g * f (x * g)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_left_comm]
    rw [he, hHharm x, hfharm x]
  have hlow (x : Γ) : ∀ᶠ n in atTop, c * (r (y n) - m) ≤ r x - m := by
    have hh := eventual_superharmonic_ratio_comparison s μ hμ hmass hgap H hH y c
      hminor (fun x => f x - m * H x) hlowpos hlowharm x
    simpa only [sub_div, mul_div_cancel_right₀ _ (ne_of_gt (hH _))] using hh
  have hupp (x : Γ) : ∀ᶠ n in atTop, c * (M - r (y n)) ≤ M - r x := by
    have hh := eventual_superharmonic_ratio_comparison s μ hμ hmass hgap H hH y c
      hminor (fun x => M * H x - f x) huppos huppharm x
    simpa only [sub_div, mul_div_cancel_right₀ _ (ne_of_gt (hH _))] using hh
  have hconst := constant_of_eventual_oscillation_comparison r y c hc hbelow habove hlow hupp
  refine ⟨r 1, hr 1, fun x => ?_⟩
  exact (div_eq_iff (ne_of_gt (hH x))).mp (hconst x 1)

end Singularity
