import Singularity.CoordinateExcursion
import Singularity.GreenKillingLoss

/-!
# Green loss for a distant coordinate sublevel

The finite-path excursion cutoff and the spectral tail estimate give an actual
exponential bound for G-G_A. The exponent depends on the spectral gap and the
jump bound; no Martin kernel or relative Ancona inequality is used.
-/

noncomputable section
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ]

/-- Explicit loss estimate for a killing set below a bounded-jump coordinate. -/
theorem coordinate_green_killing_loss_bound
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q < 1)
    (hb : ∀ n : ℕ, ‖rightMarkov s μ ^ n‖ ≤ C * q ^ n)
    (h : Γ → ℝ) (L r : ℝ) (hL : 0 < L)
    (hjump : ∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L)
    (A : Set Γ) (hA : ∀ a ∈ A, h a ≤ r) (x y : Γ) :
    walkGreen s μ x y - killedGreen s μ A x y ≤
      C / (1-q) * Real.exp (Real.log q * ((h x + h y - 2*r) / L)) := by
  apply green_killing_loss_le_real_cutoff s μ hμ hgap A x y C q hC hq hq1 hb
  intro n hn
  exact killedWeight_eq_transition_of_short_excursion s μ h L r hjump A hA n x y
    ((lt_div_iff₀ hL).mp hn)

/-- Uniform positive constants for every coordinate with the given jump bound,
every killing set below a level, and every pair of endpoints. -/
theorem coordinate_green_killing_loss_decay
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (L : ℝ) (hL : 0 < L) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (h : Γ → ℝ) (r : ℝ),
      (∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L) →
      ∀ A : Set Γ, (∀ a ∈ A, h a ≤ r) → ∀ x y : Γ,
      walkGreen s μ x y - killedGreen s μ A x y ≤
        C * Real.exp (-c * (h x + h y - 2*r)) := by
  obtain ⟨C,q,hC,hq,hq1,hb⟩ := markov_uniform_geometric_rate s μ hgap
  refine ⟨C/(1-q), -Real.log q/L, div_pos hC (sub_pos.mpr hq1),
    div_pos (neg_pos.mpr (Real.log_neg hq hq1)) hL, ?_⟩
  intro h r hjump A hA x y
  have hh := coordinate_green_killing_loss_bound s μ hμ hgap C q hC.le hq hq1 hb
    h L r hL hjump A hA x y
  have he : -(-Real.log q/L) * (h x+h y-2*r) = Real.log q*((h x+h y-2*r)/L) := by ring
  rw [he]
  exact hh

end Singularity
