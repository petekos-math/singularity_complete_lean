import Singularity.SpectralEscape
import Singularity.KilledWalk

/-!
# Spectral decay for killed Green functions

A spectral gap gives a geometric norm bound valid at every time after enlarging
the prefactor. If all paths below a cutoff are excluded, the killed Green series
is bounded by the corresponding geometric tail, uniformly in the killed set.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ]

omit [MeasurableSingletonClass Γ] in
/-- A spectral gap gives a uniform geometric bound on every operator power. -/
theorem markov_uniform_geometric_rate (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ ∀ n : ℕ, ‖rightMarkov s μ ^ n‖ ≤ C * q ^ n := by
  obtain ⟨q, hq, hq1, hb⟩ := markov_positive_geometric_rate s μ hgap
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  let C := 1 + ∑ n ∈ Finset.range N, ‖rightMarkov s μ ^ n‖ / q ^ n
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, ‖rightMarkov s μ ^ n‖ / q ^ n :=
    Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (pow_pos hq n).le)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, q, lt_of_lt_of_le zero_lt_one hC, hq, hq1, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (pow_pos hq n).le hC)
  · have hm := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.range N) => div_nonneg (norm_nonneg (rightMarkov s μ ^ k)) (pow_pos hq k).le)
      (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    apply (div_le_iff₀ (pow_pos hq n)).mp
    exact hm.trans (by dsimp [C]; linarith)

/-- Excluding every length below N bounds the killed Green kernel by the
geometric tail starting at N. -/
theorem killedGreen_le_geometric_tail (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (C q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ n : ℕ, ‖rightMarkov s μ ^ n‖ ≤ C * q ^ n)
    (A : Set Γ) (x y : Γ) (N : ℕ)
    (hzero : ∀ n < N, killedWeight s μ A n x y = 0) :
    killedGreen s μ A x y ≤ C * q ^ N / (1 - q) := by
  have hs := killedWeight_summable s μ hμ hgap A x y
  have he : killedGreen s μ A x y = ∑' n : ℕ, killedWeight s μ A (n + N) x y := by
    have h := hs.sum_add_tsum_nat_add N
    have hz : ∑ n ∈ Finset.range N, killedWeight s μ A n x y = 0 :=
      Finset.sum_eq_zero (fun n hn => hzero n (Finset.mem_range.mp hn))
    simpa only [hz, zero_add, killedGreen] using h.symm
  rw [he]
  calc
    _ ≤ ∑' n : ℕ, (C * q ^ N) * q ^ n := by
      apply Summable.tsum_le_tsum _
        ((summable_nat_add_iff N).mpr hs)
        ((summable_geometric_of_lt_one hq hq1).mul_left (C * q ^ N))
      intro n
      calc
        _ ≤ ‖rightMarkov s μ ^ (n + N)‖ :=
          (killedWeight_le_transition s μ hμ A (n + N) x y).trans
            (transitionWeight_le_power_norm s μ (n + N) x y)
        _ ≤ C * q ^ (n + N) := hb _
        _ = _ := by rw [pow_add]; ring
    _ = C * q ^ N / (1 - q) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]

/-- The real cutoff version, using the first integer at least T. -/
theorem killedGreen_le_real_cutoff (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q < 1)
    (hb : ∀ n : ℕ, ‖rightMarkov s μ ^ n‖ ≤ C * q ^ n)
    (A : Set Γ) (x y : Γ) (T : ℝ)
    (hzero : ∀ n : ℕ, (n : ℝ) < T → killedWeight s μ A n x y = 0) :
    killedGreen s μ A x y ≤ C / (1 - q) * Real.exp (Real.log q * T) := by
  have htail := killedGreen_le_geometric_tail s μ hμ hgap C q hq.le hq1 hb
    A x y ⌈T⌉₊ (fun n hn => hzero n (Nat.lt_ceil.mp hn))
  have hp : q ^ ⌈T⌉₊ ≤ Real.exp (Real.log q * T) := by
    calc
      _ = Real.exp (Real.log q * (⌈T⌉₊ : ℝ)) := by rw [mul_comm, Real.exp_nat_mul, Real.exp_log hq]
      _ ≤ _ := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (Nat.le_ceil T) (Real.log_neg hq hq1).le)
  apply htail.trans
  calc
    _ = C / (1 - q) * q ^ ⌈T⌉₊ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (div_nonneg hC (sub_pos.mpr hq1).le)

end Singularity
