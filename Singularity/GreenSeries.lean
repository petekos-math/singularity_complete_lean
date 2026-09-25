import Singularity.Green
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# The Green resolvent is the norm-convergent Green series

Gelfand's formula supplies an eventual geometric bound on the operator powers
from spectral radius < 1. This does not assume the stronger condition ‖P‖ < 1.
Identification with the random-walk path probabilities is proved in `WalkKernel.lean`
and `FiniteWalkLaw.lean`.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Singularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- An operator spectral gap implies an eventual geometric bound on the powers. -/
theorem green_powers_geometric_bound (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ᶠ n : ℕ in atTop, ‖P ^ n‖ ≤ q ^ n := by
  obtain ⟨r, hr, hr1⟩ := exists_between hgap
  have hrfin : r ≠ ⊤ := ne_top_of_lt hr1
  have hq0 : 0 ≤ r.toReal := ENNReal.toReal_nonneg
  have hq1 : r.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hrfin ENNReal.one_ne_top).mpr hr1
  refine ⟨r.toReal, hq0, hq1, ?_⟩
  have he : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (‖P ^ n‖ ^ (1 / (n : ℝ))) < r :=
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius P).eventually (gt_mem_nhds hr)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hroot : ‖P ^ n‖ ^ (1 / (n : ℝ)) ≤ r.toReal :=
    ((ENNReal.ofReal_lt_iff_lt_toReal (Real.rpow_nonneg (norm_nonneg _) _) hrfin).mp hn).le
  calc
    ‖P ^ n‖ = (‖P ^ n‖ ^ (1 / (n : ℝ))) ^ (n : ℝ) := by
      rw [← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hnpos.ne', Real.rpow_one]
    _ ≤ r.toReal ^ (n : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hroot hnpos.le
    _ = r.toReal ^ n := Real.rpow_natCast _ _

/-- The norms of the Green-series terms are summable. -/
theorem green_powers_norm_summable (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    Summable (fun n : ℕ => ‖P ^ n‖) := by
  obtain ⟨q, hq0, hq1, hbound⟩ := green_powers_geometric_bound P hgap
  apply (summable_geometric_of_lt_one hq0 hq1).of_norm_bounded_eventually_nat
  simpa only [norm_norm] using hbound

/-- Absolute norm convergence gives convergence in the operator Banach space. -/
theorem green_powers_summable (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    Summable (fun n : ℕ => P ^ n) :=
  (green_powers_norm_summable P hgap).of_norm

/-- The sum of the operator powers is exactly the previously constructed resolvent. -/
theorem green_eq_tsum (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    green P = ∑' n : ℕ, P ^ n := by
  have hs := green_powers_summable P hgap
  calc
    green P = green P * ((1 - P) * ∑' n : ℕ, P ^ n) := by
      rw [hs.one_sub_mul_tsum_pow, mul_one]
    _ = ∑' n : ℕ, P ^ n := by
      rw [← mul_assoc]
      change Ring.inverse (1 - P) * (1 - P) * _ = _
      rw [Ring.inverse_mul_cancel (1 - P) (one_sub_isUnit P hgap), one_mul]

/-- The Green series converges in operator norm to the resolvent. -/
theorem green_hasSum (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    HasSum (fun n : ℕ => P ^ n) (green P) := by
  rw [green_eq_tsum P hgap]
  exact (green_powers_summable P hgap).hasSum

/-- Finite-time Green operators converge in norm. -/
theorem green_partial_sums_tendsto (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, P ^ n) atTop (𝓝 (green P)) :=
  (green_hasSum P hgap).tendsto_sum_nat

/-- Evaluation at a vector commutes with the norm-convergent Green series. -/
theorem green_apply_hasSum (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) (v : E) :
    HasSum (fun n : ℕ => (P ^ n) v) (green P v) :=
  (ContinuousLinearMap.apply ℂ E v).hasSum (green_hasSum P hgap)

/-- Every matrix coefficient is the sum of the corresponding coefficients of Pⁿ. -/
theorem green_pairing_hasSum (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) (u v : E) :
    HasSum (fun n : ℕ => inner ℂ u ((P ^ n) v)) (inner ℂ u (green P v)) :=
  (innerSL ℂ u).hasSum (green_apply_hasSum P hgap v)

/-- Absolute convergence of each scalar Green-series coefficient. -/
theorem green_pairing_norm_summable (P : E →L[ℂ] E)
    (hgap : spectralRadius ℂ P < 1) (u v : E) :
    Summable (fun n : ℕ => ‖inner ℂ u ((P ^ n) v)‖) := by
  have hbound := ((green_powers_norm_summable P hgap).mul_right ‖v‖).mul_left ‖u‖
  apply hbound.of_norm_bounded_eventually_nat
  exact Filter.Eventually.of_forall (fun n => by
    rw [norm_norm]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left ((P ^ n).le_opNorm v) (norm_nonneg u)))

end Singularity
