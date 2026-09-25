import Singularity.WalkKernel

/-!
# First-entrance path sums

A word contributes to first entrance at time n when all its positions at times
0,...,n-1 lie outside A and its endpoint lies in A. For a∈A this gives the
entry F(x,a), including the time-zero convention F(a,a)=1.

The total first-entrance series is proved convergent and dominated by G.
The bounded-operator realization and renewal identity are proved in
`EntranceOperator.lean`. The infinite-path stopping-time interpretation remains
separate from these finite-path constructions.
-/

noncomputable section
open scoped BigOperators Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Avoidance at every time strictly before the endpoint. -/
def avoidsBefore (s : Finset Γ) (A : Set Γ) : (n : ℕ) → Γ → WalkWord s n → Prop
  | 0, _, _ => True
  | n + 1, x, w => x ∉ A ∧ avoidsBefore s A n (x * w.1) w.2

/-- Weight of the length-n paths whose first entrance into A is at a. -/
def firstEntranceWeight (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ)
    (n : ℕ) (x a : Γ) : ℝ :=
  ∑ w : WalkWord s n, if avoidsBefore s A n x w ∧ walkEndpoint s n x w = a ∧ a ∈ A
    then walkWeight s μ n w else 0

/-- First-entrance weights are nonnegative. -/
theorem firstEntranceWeight_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (A : Set Γ) (n : ℕ) (x a : Γ) :
    0 ≤ firstEntranceWeight s μ A n x a := by
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact walkWeight_nonneg s μ hμ n w
  · exact le_rfl

/-- Restricting to first-entrance paths can only decrease the transition weight. -/
theorem firstEntranceWeight_le_transition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (A : Set Γ) (n : ℕ) (x a : Γ) :
    firstEntranceWeight s μ A n x a ≤ transitionWeight s μ n x a := by
  apply Finset.sum_le_sum
  intro w _
  by_cases h : avoidsBefore s A n x w ∧ walkEndpoint s n x w = a ∧ a ∈ A
  · simp [h]
  · rw [ite_eq_right_iff.mpr (fun hp => (h hp).elim)]
    split_ifs
    · exact walkWeight_nonneg s μ hμ n w
    · exact le_rfl

/-- The time-zero convention includes a starting point already in A. -/
theorem firstEntranceWeight_zero (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x a : Γ) :
    firstEntranceWeight s μ A 0 x a = if x = a ∧ a ∈ A then 1 else 0 := by
  simp only [firstEntranceWeight, avoidsBefore, walkEndpoint, walkWeight, true_and]
  change (∑ _ : PUnit, if x = a ∧ a ∈ A then (1 : ℝ) else 0) = _
  simp

/-- Starting inside A excludes any positive first-entrance time. -/
theorem firstEntranceWeight_succ_of_mem (s : Finset Γ) (μ : Γ → ℝ)
    (A : Set Γ) {x : Γ} (hx : x ∈ A) (n : ℕ) (a : Γ) :
    firstEntranceWeight s μ A (n + 1) x a = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  simp only [avoidsBefore, hx, not_true_eq_false, false_and, ite_false]

/-- Outside A, first entrance after n+1 jumps is determined by the first jump. -/
theorem firstEntranceWeight_succ_of_notMem (s : Finset Γ) (μ : Γ → ℝ)
    (A : Set Γ) {x : Γ} (hx : x ∉ A) (n : ℕ) (a : Γ) :
    firstEntranceWeight s μ A (n + 1) x a =
      ∑ g ∈ s, μ g * firstEntranceWeight s μ A n (x * g) a := by
  unfold firstEntranceWeight
  rw [← Finset.sum_coe_sort s]
  change (∑ w : s × WalkWord s n,
      if avoidsBefore s A (n + 1) x w ∧ walkEndpoint s (n + 1) x w = a ∧ a ∈ A
      then walkWeight s μ (n + 1) w else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [avoidsBefore, walkEndpoint, walkWeight, hx, not_false_eq_true, true_and]
  split_ifs <;> simp

/-- The first-entrance kernel defined by the convergent nonnegative path series. -/
def firstEntranceKernel (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x a : Γ) : ℝ :=
  ∑' n : ℕ, firstEntranceWeight s μ A n x a

/-- Nonnegativity of the first-entrance kernel. -/
theorem firstEntranceKernel_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (A : Set Γ) (x a : Γ) :
    0 ≤ firstEntranceKernel s μ A x a :=
  tsum_nonneg (fun n => firstEntranceWeight_nonneg s μ hμ A n x a)

/-- For x∈A the kernel is the identity, rather than a first-positive-return kernel. -/
theorem firstEntranceKernel_of_mem (s : Finset Γ) (μ : Γ → ℝ)
    (A : Set Γ) {x : Γ} (hx : x ∈ A) (a : Γ) :
    firstEntranceKernel s μ A x a = if x = a then 1 else 0 := by
  rw [firstEntranceKernel, tsum_eq_single 0]
  · rw [firstEntranceWeight_zero]
    by_cases hxa : x = a
    · subst a
      simp [hx]
    · simp [hxa]
  · intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => exact firstEntranceWeight_succ_of_mem s μ A hx n a

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]

/-- The first-entrance series converges, by domination by the Green series. -/
theorem firstEntranceWeight_summable (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (x a : Γ) : Summable (fun n : ℕ => firstEntranceWeight s μ A n x a) := by
  apply (walkGreen_summable s μ hgap x a).of_norm_bounded_eventually_nat
  exact Filter.Eventually.of_forall (fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (firstEntranceWeight_nonneg s μ hμ A n x a)]
    exact firstEntranceWeight_le_transition s μ hμ A n x a)

/-- Entrywise domination F(x,a)≤G(x,a), with summability justified. -/
theorem firstEntranceKernel_le_green (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (x a : Γ) : firstEntranceKernel s μ A x a ≤ walkGreen s μ x a :=
  Summable.tsum_le_tsum (fun n => firstEntranceWeight_le_transition s μ hμ A n x a)
    (firstEntranceWeight_summable s μ hμ hgap A x a) (walkGreen_summable s μ hgap x a)

/-- The first-entrance kernel is P-harmonic outside A. All sums are convergent. -/
theorem firstEntranceKernel_harmonic (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) {x : Γ} (hx : x ∉ A) (a : Γ) :
    firstEntranceKernel s μ A x a = ∑ g ∈ s, μ g * firstEntranceKernel s μ A (x * g) a := by
  have hzero : firstEntranceWeight s μ A 0 x a = 0 := by
    rw [firstEntranceWeight_zero]
    split_ifs with h
    · exact (hx (h.1 ▸ h.2)).elim
    · rfl
  rw [firstEntranceKernel, (firstEntranceWeight_summable s μ hμ hgap A x a).tsum_eq_zero_add,
    hzero, zero_add]
  simp_rw [firstEntranceWeight_succ_of_notMem s μ A hx]
  rw [Summable.tsum_finsetSum (fun g _ =>
    (firstEntranceWeight_summable s μ hμ hgap A (x * g) a).mul_left (μ g))]
  simp only [firstEntranceKernel, tsum_mul_left]

end Singularity
