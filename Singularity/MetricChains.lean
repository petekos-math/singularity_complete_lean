import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Finite chains with controlled metric increments

Concatenation and subdivision of an isometrically parametrized interval are
used to construct short chains in the hyperbolic plane.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {X : Type*} [PseudoMetricSpace X]

/-- Concatenation preserves a common jump bound and adds the numbers of steps. -/
theorem metric_chain_append (f g : ℕ → X) (n m : ℕ) (L : ℝ)
    (hjoin : f n = g 0)
    (hf : ∀ k < n, dist (f k) (f (k + 1)) ≤ L)
    (hg : ∀ k < m, dist (g k) (g (k + 1)) ≤ L) :
    ∃ h : ℕ → X, h 0 = f 0 ∧ h (n + m) = g m ∧
      ∀ k < n + m, dist (h k) (h (k + 1)) ≤ L := by
  let h : ℕ → X := fun k => if k ≤ n then f k else g (k - n)
  refine ⟨h, by simp [h], ?_, ?_⟩
  · by_cases hm : m = 0
    · subst m; simpa [h] using hjoin
    · simp [h, show ¬n + m ≤ n by omega]
  · intro k hk
    by_cases hkn : k < n
    · simpa only [h, ite_eq_left (Nat.le_of_lt hkn), ite_eq_left (show k + 1 ≤ n by omega)] using hf k hkn
    · by_cases he : k = n
      · subst k
        simpa [h, hjoin] using hg 0 (by omega)
      · have hn : n < k := by omega
        have hj := hg (k - n) (by omega)
        simpa only [h, ite_eq_right (show ¬k ≤ n by omega),
          ite_eq_right (show ¬k + 1 ≤ n by omega), show k + 1 - n = k - n + 1 by omega] using hj

/-- An isometric real interval admits unit-step subdivision with fewer than
length plus two steps. A positive number of steps also covers coinciding ends. -/
theorem isometry_interval_chain (f : ℝ → X) (hf : Isometry f) (a b : ℝ) :
    ∃ (n : ℕ) (p : ℕ → X), p 0 = f a ∧ p n = f b ∧
      (n : ℝ) ≤ |b - a| + 2 ∧ ∀ k < n, dist (p k) (p (k + 1)) ≤ 1 := by
  let n := ⌈|b - a|⌉₊ + 1
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hlen : |b - a| ≤ (n : ℝ) := by
    have h := Nat.le_ceil |b - a|
    dsimp [n]; push_cast; linarith
  let p : ℕ → X := fun k => f (a + (b - a) * (k : ℝ) / n)
  refine ⟨n, p, by simp [p], ?_, ?_, ?_⟩
  · dsimp [p]
    congr 1
    field_simp
    ring
  · have h := Nat.ceil_lt_add_one (abs_nonneg (b - a))
    dsimp [n]; push_cast; linarith
  · intro k _
    dsimp [p]
    rw [hf.dist_eq, Real.dist_eq]
    have he : (a + (b - a) * (k : ℝ) / n) -
        (a + (b - a) * ((k + 1 : ℕ) : ℝ) / n) = -(b - a) / n := by push_cast; ring
    rw [he, abs_div, abs_neg, abs_of_pos hn]
    exact (div_le_one hn).mpr hlen

end Singularity
