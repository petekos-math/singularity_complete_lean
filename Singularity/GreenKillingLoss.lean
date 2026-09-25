import Singularity.KilledGreenDecay

/-!
# Spectral bounds for the Green mass removed by killing

The difference G-G_A is the convergent sum of transition mass removed at each
time. If killing removes no mass before N, its whole effect is bounded by the
spectral tail from N onwards. This estimates the error in retaining paths in a
domain, rather than the Green kernel of paths staying outside a ball.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (x y : Γ)

include hμ hgap

/-- Subtracting the absolutely convergent path series gives exactly the loss. -/
theorem green_killing_loss_eq_tsum :
    walkGreen s μ x y - killedGreen s μ A x y =
      ∑' n : ℕ, (transitionWeight s μ n x y - killedWeight s μ A n x y) := by
  exact ((walkGreen_summable s μ hgap x y).tsum_sub
    (killedWeight_summable s μ hμ hgap A x y)).symm

/-- If no short paths are lost, the Green loss is bounded by a geometric tail. -/
theorem green_killing_loss_le_geometric_tail
    (C q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ n : ℕ, ‖rightMarkov s μ ^ n‖ ≤ C * q ^ n) (N : ℕ)
    (heq : ∀ n < N, killedWeight s μ A n x y = transitionWeight s μ n x y) :
    walkGreen s μ x y - killedGreen s μ A x y ≤ C * q ^ N / (1-q) := by
  let f := fun n : ℕ => transitionWeight s μ n x y - killedWeight s μ A n x y
  have hs : Summable f := (walkGreen_summable s μ hgap x y).sub
    (killedWeight_summable s μ hμ hgap A x y)
  have he : (∑' n : ℕ, f n) = ∑' n : ℕ, f (n+N) := by
    have hh := hs.sum_add_tsum_nat_add N
    have hz : ∑ n ∈ Finset.range N, f n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      dsimp [f]
      rw [heq n (Finset.mem_range.mp hn), sub_self]
    simpa only [hz, zero_add] using hh.symm
  rw [green_killing_loss_eq_tsum s μ hμ hgap A x y]
  change (∑' n : ℕ, f n) ≤ _
  rw [he]
  calc
    _ ≤ ∑' n : ℕ, (C * q ^ N) * q ^ n := by
      apply Summable.tsum_le_tsum _ ((summable_nat_add_iff N).mpr hs)
        ((summable_geometric_of_lt_one hq hq1).mul_left (C * q ^ N))
      intro n
      calc
        f (n+N) ≤ transitionWeight s μ (n+N) x y :=
          sub_le_self _ (killedWeight_nonneg s μ hμ A (n+N) x y)
        _ ≤ ‖rightMarkov s μ ^ (n+N)‖ := transitionWeight_le_power_norm s μ (n+N) x y
        _ ≤ C * q ^ (n+N) := hb _
        _ = _ := by rw [pow_add]; ring
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]

/-- A real cutoff for the earliest possible removed path. -/
theorem green_killing_loss_le_real_cutoff
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q < 1)
    (hb : ∀ n : ℕ, ‖rightMarkov s μ ^ n‖ ≤ C * q ^ n) (T : ℝ)
    (heq : ∀ n : ℕ, (n : ℝ) < T → killedWeight s μ A n x y = transitionWeight s μ n x y) :
    walkGreen s μ x y - killedGreen s μ A x y ≤
      C / (1-q) * Real.exp (Real.log q * T) := by
  have hh := green_killing_loss_le_geometric_tail s μ hμ hgap A x y C q hq.le hq1 hb
    ⌈T⌉₊ (fun n hn => heq n (Nat.lt_ceil.mp hn))
  have hp : q ^ ⌈T⌉₊ ≤ Real.exp (Real.log q * T) := by
    calc
      _ = Real.exp (Real.log q * (⌈T⌉₊ : ℝ)) := by rw [mul_comm, Real.exp_nat_mul, Real.exp_log hq]
      _ ≤ _ := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (Nat.le_ceil T) (Real.log_neg hq hq1).le)
  apply hh.trans
  calc
    _ = C / (1-q) * q ^ ⌈T⌉₊ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (div_nonneg hC (sub_pos.mpr hq1).le)

end Singularity
