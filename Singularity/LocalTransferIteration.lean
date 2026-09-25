import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Accumulating errors in local positive transfer steps

A transfer only needs to preserve inequalities from the next admissible state
set to the current one. If its loss on G is relatively small and it decreases
a comparison potential P, the total loss over finitely many steps is bounded
by the sum of the step errors. No global inequality outside these sets is used.
-/

noncomputable section
open scoped Classical

namespace Singularity

/-- Local positive transfers accumulate at most the sum of their relative errors. -/
theorem local_transfer_error_bound {ι : Type*} (N : ℕ)
    (T : ℕ → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (S : ℕ → Set ι) (ε : ℕ → ℝ)
    (G P : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hG : ∀ z, 0 ≤ G z)
    (hε : ∀ n < N, 0 ≤ ε n) (hsum : ∑ n ∈ Finset.range N, ε n ≤ 1)
    (hmono : ∀ n < N, ∀ f g : ι → ℝ,
      (∀ z ∈ S (n + 1), f z ≤ g z) → ∀ z ∈ S n, T n f z ≤ T n g z)
    (hP : ∀ n < N, ∀ z ∈ S n, T n P z ≤ P z)
    (herror : ∀ n < N, ∀ z ∈ S n, G z - T n G z ≤ ε n * G z)
    (hterminal : ∀ z ∈ S N, G z ≤ C * P z) :
    ∀ z ∈ S 0, (1 - ∑ n ∈ Finset.range N, ε n) * G z ≤ C * P z := by
  induction N generalizing T S ε with
  | zero => simpa using hterminal
  | succ N ih =>
    let e := ∑ n ∈ Finset.range N, ε (n + 1)
    have he0 : 0 ≤ e := Finset.sum_nonneg (fun n hn => hε (n + 1) (by have := Finset.mem_range.mp hn; omega))
    have heq : ∑ n ∈ Finset.range (N + 1), ε n = e + ε 0 := Finset.sum_range_succ' _ _
    have hε0 : 0 ≤ ε 0 := hε 0 (Nat.zero_lt_succ N)
    have he1 : e ≤ 1 := by rw [heq] at hsum; linarith
    have hi : ∀ z ∈ S 1, (1 - e) * G z ≤ C * P z := by
      apply ih (fun n => T (n + 1)) (fun n => S (n + 1)) (fun n => ε (n + 1))
      · intro n hn; exact hε (n + 1) (by omega)
      · exact he1
      · intro n hn f g hh z hz
        exact hmono (n + 1) (by omega) f g hh z hz
      · intro n hn z hz
        exact hP (n + 1) (by omega) z hz
      · intro n hn z hz
        exact herror (n + 1) (by omega) z hz
      · exact hterminal
    intro z hz
    have ht := hmono 0 (Nat.zero_lt_succ N) ((1 - e) • G) (C • P) hi z hz
    simp only [map_smul, Pi.smul_apply, smul_eq_mul] at ht
    have hp := mul_le_mul_of_nonneg_left (hP 0 (Nat.zero_lt_succ N) z hz) hC
    have herr := mul_le_mul_of_nonneg_left (herror 0 (Nat.zero_lt_succ N) z hz)
      (show 0 ≤ 1 - e by linarith)
    have hslack := mul_nonneg (mul_nonneg he0 hε0) (hG z)
    rw [heq]
    nlinarith

/-- Total relative loss at most one half gives a uniform factor-two comparison. -/
theorem local_transfer_half_error_bound {ι : Type*} (N : ℕ)
    (T : ℕ → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (S : ℕ → Set ι) (ε : ℕ → ℝ)
    (G P : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hG : ∀ z, 0 ≤ G z)
    (hε : ∀ n < N, 0 ≤ ε n) (hsum : ∑ n ∈ Finset.range N, ε n ≤ 1 / 2)
    (hmono : ∀ n < N, ∀ f g : ι → ℝ,
      (∀ z ∈ S (n + 1), f z ≤ g z) → ∀ z ∈ S n, T n f z ≤ T n g z)
    (hP : ∀ n < N, ∀ z ∈ S n, T n P z ≤ P z)
    (herror : ∀ n < N, ∀ z ∈ S n, G z - T n G z ≤ ε n * G z)
    (hterminal : ∀ z ∈ S N, G z ≤ C * P z) :
    ∀ z ∈ S 0, G z ≤ 2 * C * P z := by
  have hh := local_transfer_error_bound N T S ε G P C hC hG hε (by linarith)
    hmono hP herror hterminal
  intro z hz
  have hslack := mul_nonneg (show 0 ≤ 1 / 2 - ∑ n ∈ Finset.range N, ε n by linarith) (hG z)
  have h := hh z hz
  nlinarith

end Singularity
