import Singularity.CountingL2
import Singularity.GreenSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite jump paths and the random-walk Green kernel

A length-n path is an ordered n-tuple of jumps from the given finite support.
Its weight is the product of the jump weights. Transition coefficients sum
these weights over paths with a specified endpoint. This file relates these
finite path sums to the actual counting-measure Markov operator.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace Singularity

universe u

/-- Ordered finite words, written recursively to expose the first jump. -/
def WalkWord (S : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => S × WalkWord S n

instance walkWordFintype (S : Type*) [Fintype S] : (n : ℕ) → Fintype (WalkWord S n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd S (WalkWord S n) _ (walkWordFintype S n)

variable {Γ : Type*} [Group Γ]

/-- The endpoint after multiplying the successive jumps on the right. -/
def walkEndpoint (s : Finset Γ) : (n : ℕ) → Γ → WalkWord s n → Γ
  | 0, x, _ => x
  | n + 1, x, w => walkEndpoint s n (x * w.1) w.2

/-- Product of the weights of the successive jumps. -/
def walkWeight (s : Finset Γ) (μ : Γ → ℝ) : (n : ℕ) → WalkWord s n → ℝ
  | 0, _ => 1
  | n + 1, w => μ w.1 * walkWeight s μ n w.2

/-- The n-step transition weight, defined by summing the actual finite paths. -/
def transitionWeight (s : Finset Γ) (μ : Γ → ℝ) (n : ℕ) (x y : Γ) : ℝ :=
  ∑ w : WalkWord s n, if walkEndpoint s n x w = y then walkWeight s μ n w else 0

omit [Group Γ] in
/-- All path weights are nonnegative for a nonnegative jump law. -/
theorem walkWeight_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (n : ℕ) (w : WalkWord s n) :
    0 ≤ walkWeight s μ n w := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hμ w.1 w.1.property) (ih w.2)

omit [Group Γ] in
/-- The total weight of all length-n paths is one for a probability jump law. -/
theorem walkWeight_mass (s : Finset Γ) (μ : Γ → ℝ)
    (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) :
    ∑ w : WalkWord s n, walkWeight s μ n w = 1 := by
  induction n with
  | zero =>
    change ∑ _ : PUnit, (1 : ℝ) = 1
    simp
  | succ n ih =>
    change ∑ w : s × WalkWord s n, μ w.1 * walkWeight s μ n w.2 = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    simpa only [Finset.sum_coe_sort] using hmass

/-- Transition coefficients are nonnegative. -/
theorem transitionWeight_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (n : ℕ) (x y : Γ) : 0 ≤ transitionWeight s μ n x y := by
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact walkWeight_nonneg s μ hμ n w
  · exact le_rfl

/-- Each transition coefficient is at most one. -/
theorem transitionWeight_le_one (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (n : ℕ) (x y : Γ) : transitionWeight s μ n x y ≤ 1 := by
  rw [← walkWeight_mass s μ hmass n]
  apply Finset.sum_le_sum
  intro w _
  split_ifs
  · exact le_rfl
  · exact walkWeight_nonneg s μ hμ n w

/-- The endpoint distribution has total mass one. -/
theorem transitionWeight_hasSum_one (s : Finset Γ) (μ : Γ → ℝ)
    (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) (x : Γ) :
    HasSum (transitionWeight s μ n x) 1 := by
  have h (w : WalkWord s n) :
      HasSum (fun y => if walkEndpoint s n x w = y then walkWeight s μ n w else 0)
        (walkWeight s μ n w) := by
    simpa only [eq_comm] using hasSum_ite_eq (walkEndpoint s n x w) (walkWeight s μ n w)
  have hs := hasSum_sum (s := Finset.univ) (fun w _ => h w)
  change HasSum (fun y => ∑ w : WalkWord s n,
    if walkEndpoint s n x w = y then walkWeight s μ n w else 0) 1
  simpa only [walkWeight_mass s μ hmass n] using hs

/-- At time zero the walk is at its starting point. -/
theorem transitionWeight_zero (s : Finset Γ) (μ : Γ → ℝ) (x y : Γ) :
    transitionWeight s μ 0 x y = if x = y then 1 else 0 := by
  change (∑ _ : PUnit, if x = y then (1 : ℝ) else 0) = _
  simp

/-- Moving the starting point on the left moves every path endpoint on the left. -/
theorem walkEndpoint_left (s : Finset Γ) (n : ℕ) (z x : Γ) (w : WalkWord s n) :
    walkEndpoint s n (z * x) w = z * walkEndpoint s n x w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change walkEndpoint s n (z * x * w.1) w.2 = z * walkEndpoint s n (x * w.1) w.2
    rw [mul_assoc, ih]

/-- Left invariance of the n-step transition kernel. -/
theorem transitionWeight_left (s : Finset Γ) (μ : Γ → ℝ) (n : ℕ) (z x y : Γ) :
    transitionWeight s μ n (z * x) (z * y) = transitionWeight s μ n x y := by
  simp only [transitionWeight, walkEndpoint_left, mul_left_cancel_iff]

variable [MeasurableSpace Γ] [MeasurableMul Γ]

/-- Under counting measure, the a.e. formula is a pointwise identity. -/
theorem rightMarkov_apply (s : Finset Γ) (μ : Γ → ℝ) (f : GroupL2 Γ) (x : Γ) :
    rightMarkov s μ f x = ∑ g ∈ s, (μ g : ℂ) * f (x * g) :=
  Measure.ae_count_iff.mp (rightMarkov_apply_ae s μ f) x

/-- Powers of the actual Markov operator sum over the length-n paths. -/
theorem rightMarkov_pow_apply (s : Finset Γ) (μ : Γ → ℝ) (n : ℕ)
    (f : GroupL2 Γ) (x : Γ) :
    (rightMarkov s μ ^ n) f x =
      ∑ w : WalkWord s n, (walkWeight s μ n w : ℂ) * f (walkEndpoint s n x w) := by
  induction n generalizing x with
  | zero =>
    change f x = ∑ _ : PUnit, (1 : ℂ) * f x
    simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, rightMarkov_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [← Finset.sum_coe_sort s]
    change (∑ g : s, ∑ w : WalkWord s n,
      (μ g : ℂ) * ((walkWeight s μ n w : ℂ) * f (walkEndpoint s n (x * g) w))) =
      ∑ w : s × WalkWord s n,
        (μ w.1 * walkWeight s μ n w.2 : ℝ) * f (walkEndpoint s n (x * w.1) w.2)
    rw [Fintype.sum_prod_type]
    simp only [Complex.ofReal_mul, mul_assoc]

variable [MeasurableSingletonClass Γ]

/-- The n-step path kernel is the matrix coefficient of Pⁿ. -/
theorem rightMarkov_pow_delta (s : Finset Γ) (μ : Γ → ℝ) (n : ℕ) (x y : Γ) :
    (rightMarkov s μ ^ n) (countingDelta y) x = (transitionWeight s μ n x y : ℂ) := by
  rw [rightMarkov_pow_apply, transitionWeight, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [countingDelta_apply]
  split_ifs <;> simp

/-- The path-counting Green kernel. Finiteness is proved from the operator gap below. -/
def walkGreen (s : Finset Γ) (μ : Γ → ℝ) (x y : Γ) : ℝ :=
  ∑' n : ℕ, transitionWeight s μ n x y

/-- The complex path series converges to the actual resolvent coefficient. -/
theorem walkGreen_coefficient_hasSum (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    HasSum (fun n : ℕ => (transitionWeight s μ n x y : ℂ))
      (green (rightMarkov s μ) (countingDelta y) x) := by
  have h := (countingEvaluation x).hasSum
    (green_apply_hasSum (rightMarkov s μ) hgap (countingDelta y))
  simpa only [countingEvaluation_apply, rightMarkov_pow_delta] using h

/-- In particular, the real path-counting series is summable. -/
theorem walkGreen_summable (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    Summable (fun n : ℕ => transitionWeight s μ n x y) := by
  have h := Complex.reCLM.hasSum (walkGreen_coefficient_hasSum s μ hgap x y)
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using h.summable

/-- This identifies the probabilistic Green kernel with the operator resolvent. -/
theorem walkGreen_eq_coefficient (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    (walkGreen s μ x y : ℂ) = green (rightMarkov s μ) (countingDelta y) x := by
  rw [walkGreen, Complex.ofReal_tsum]
  exact (walkGreen_coefficient_hasSum s μ hgap x y).tsum_eq

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] in
/-- A nonnegative jump law has nonnegative Green coefficients. -/
theorem walkGreen_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (x y : Γ) : 0 ≤ walkGreen s μ x y :=
  tsum_nonneg (fun n => transitionWeight_nonneg s μ hμ n x y)

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] in
/-- The path Green kernel is left invariant. -/
theorem walkGreen_left (s : Finset Γ) (μ : Γ → ℝ) (z x y : Γ) :
    walkGreen s μ (z * x) (z * y) = walkGreen s μ x y := by
  simp only [walkGreen, transitionWeight_left]

/-- The operator bound controls every Green-kernel entry. -/
theorem walkGreen_abs_le (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    |walkGreen s μ x y| ≤ ‖green (rightMarkov s μ)‖ := by
  calc
    |walkGreen s μ x y| = ‖(walkGreen s μ x y : ℂ)‖ := by simp
    _ = ‖green (rightMarkov s μ) (countingDelta y) x‖ := by rw [walkGreen_eq_coefficient s μ hgap]
    _ ≤ ‖green (rightMarkov s μ) (countingDelta y)‖ := countingEvaluation_le x _
    _ ≤ ‖green (rightMarkov s μ)‖ * ‖countingDelta y‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖green (rightMarkov s μ)‖ := by rw [countingDelta_norm, mul_one]

/-- Every diagonal Green entry includes the initial visit. -/
theorem walkGreen_diag_ge_one (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) :
    1 ≤ walkGreen s μ x x := by
  have h := (walkGreen_summable s μ hgap x x).le_tsum 0
    (fun n _ => transitionWeight_nonneg s μ hμ n x x)
  simpa [transitionWeight_zero, walkGreen] using h

/-- First-step renewal for the actual path-counting Green kernel. -/
theorem walkGreen_first_step (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    walkGreen s μ x y = (if x = y then 1 else 0) +
      ∑ g ∈ s, μ g * walkGreen s μ (x * g) y := by
  have h := congrArg (countingEvaluation x)
    (green_right_inverse (rightMarkov s μ) hgap (countingDelta y))
  rw [map_sub] at h
  simp only [countingEvaluation_apply, rightMarkov_apply, countingDelta_apply] at h
  simp_rw [← walkGreen_eq_coefficient s μ hgap] at h
  apply Complex.ofReal_injective
  push_cast
  by_cases hxy : x = y
  · simpa [hxy] using sub_eq_iff_eq_add.mp h
  · simpa [hxy] using sub_eq_iff_eq_add.mp h

end Singularity
