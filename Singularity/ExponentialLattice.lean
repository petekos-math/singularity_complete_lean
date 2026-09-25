import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Uniform bounds for exponential lattice translates

This supplies the overlap estimate for the logarithmic hitting densities.
The bound is deliberately not optimized: only finiteness and uniformity matter.
-/

noncomputable section
open scoped BigOperators

namespace Singularity

/-- Exponential decay on both ends of the integer lattice is summable. -/
theorem summable_exp_abs_int {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℤ => Real.exp (-τ * |(n : ℝ)|)) := by
  have hn : Summable (fun n : ℕ => Real.exp (-τ * (n : ℝ))) := by
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hτ)
  apply Summable.of_nat_of_neg
  · simpa using hn
  · simpa using hn

/-- The square of any constant multiple of this envelope is summable. -/
theorem summable_exp_abs_int_sq {τ : ℝ} (hτ : 0 < τ) (C : ℝ) :
    Summable (fun n : ℤ => (C * Real.exp (-τ * |(n : ℝ)|)) ^ 2) := by
  have h : Summable (fun n : ℤ => C ^ 2 * Real.exp (-(2 * τ) * |(n : ℝ)|)) :=
    (summable_exp_abs_int (show 0 < 2 * τ by positivity)).mul_left (C ^ 2)
  have heq : (fun n : ℤ => (C * Real.exp (-τ * |(n : ℝ)|)) ^ 2) =
      (fun n : ℤ => C ^ 2 * Real.exp (-(2 * τ) * |(n : ℝ)|)) := by
    funext n
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [heq]
  exact h

/-- A finite positive constant that bounds every translated exponential sum. -/
def latticeEnvelopeBound (τ : ℝ) : ℝ :=
  Real.exp τ * ∑' n : ℤ, Real.exp (-τ * |(n : ℝ)|)

theorem latticeEnvelopeBound_nonneg (τ : ℝ) : 0 ≤ latticeEnvelopeBound τ := by
  unfold latticeEnvelopeBound
  exact mul_nonneg (Real.exp_nonneg _) (tsum_nonneg (fun _ => Real.exp_nonneg _))

/-- The local comparison after choosing the lattice cell containing `t`. -/
theorem exp_translate_le_cell_envelope {τ : ℝ} (hτ : 0 < τ) (t : ℝ) (n : ℤ) :
    Real.exp (-|t - (n : ℝ) * τ|) ≤
      Real.exp τ * Real.exp (-τ * |((n - ⌊t / τ⌋ : ℤ) : ℝ)|) := by
  let m : ℤ := ⌊t / τ⌋
  have hlo : (m : ℝ) * τ ≤ t := (le_div_iff₀ hτ).mp (Int.floor_le (t / τ))
  have hhi : t < ((m : ℝ) + 1) * τ :=
    (div_lt_iff₀ hτ).mp (Int.lt_floor_add_one (t / τ))
  have hr : |t - (m : ℝ) * τ| ≤ τ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  have htri := norm_sub_le (t - (m : ℝ) * τ) (t - (n : ℝ) * τ)
  simp only [Real.norm_eq_abs] at htri
  have hdist : |(t - (m : ℝ) * τ) - (t - (n : ℝ) * τ)| =
      τ * |((n - m : ℤ) : ℝ)| := by
    rw [Int.cast_sub]
    have heq : t - (m : ℝ) * τ - (t - (n : ℝ) * τ) =
        τ * ((n : ℝ) - (m : ℝ)) := by ring
    rw [heq, abs_mul, abs_of_pos hτ]
  rw [hdist] at htri
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change -|t - (n : ℝ) * τ| ≤ τ + -τ * |((n - m : ℤ) : ℝ)|
  linarith

/-- Every finite sub-sum of the translated exponential profiles obeys the
same bound, independently of `t`. -/
theorem sum_exp_lattice_le {τ : ℝ} (hτ : 0 < τ) (t : ℝ) (s : Finset ℤ) :
    ∑ n ∈ s, Real.exp (-|t - (n : ℝ) * τ|) ≤ latticeEnvelopeBound τ := by
  let m : ℤ := ⌊t / τ⌋
  have hsum : Summable (fun n : ℤ => Real.exp (-τ * |((n - m : ℤ) : ℝ)|)) :=
    (Equiv.subRight m).summable_iff.mpr (summable_exp_abs_int hτ)
  calc
    ∑ n ∈ s, Real.exp (-|t - (n : ℝ) * τ|) ≤
        ∑ n ∈ s, Real.exp τ * Real.exp (-τ * |((n - m : ℤ) : ℝ)|) :=
      Finset.sum_le_sum (fun n _ => exp_translate_le_cell_envelope hτ t n)
    _ = Real.exp τ * ∑ n ∈ s, Real.exp (-τ * |((n - m : ℤ) : ℝ)|) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp τ * ∑' n : ℤ, Real.exp (-τ * |((n - m : ℤ) : ℝ)|) :=
      mul_le_mul_of_nonneg_left
        (hsum.sum_le_tsum s (fun _ _ => Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = latticeEnvelopeBound τ := by
      unfold latticeEnvelopeBound
      congr 1
      exact (Equiv.subRight m).tsum_eq (fun n : ℤ => Real.exp (-τ * |(n : ℝ)|))

end Singularity
