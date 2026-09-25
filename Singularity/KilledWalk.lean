import Singularity.FirstEntranceColumn

/-!
# Green paths avoiding a subset

The killed path kernel counts precisely the paths whose positions, including
both endpoints, are all outside A. Its columns belong to ℓ² by domination by G.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Weight of length-n paths that avoid A, including at the endpoint. -/
def killedWeight (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (n : ℕ) (x y : Γ) : ℝ :=
  ∑ w : WalkWord s n, if avoidsBefore s A n x w ∧ walkEndpoint s n x w = y ∧ y ∉ A
    then walkWeight s μ n w else 0

theorem killedWeight_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (A : Set Γ) (n : ℕ) (x y : Γ) :
    0 ≤ killedWeight s μ A n x y := by
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact walkWeight_nonneg s μ hμ n w
  · exact le_rfl

theorem killedWeight_le_transition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (A : Set Γ) (n : ℕ) (x y : Γ) :
    killedWeight s μ A n x y ≤ transitionWeight s μ n x y := by
  apply Finset.sum_le_sum
  intro w _
  by_cases h : avoidsBefore s A n x w ∧ walkEndpoint s n x w = y ∧ y ∉ A
  · simp [h]
  · rw [ite_eq_right_iff.mpr (fun hp => (h hp).elim)]
    split_ifs
    · exact walkWeight_nonneg s μ hμ n w
    · exact le_rfl

theorem killedWeight_zero (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x y : Γ) :
    killedWeight s μ A 0 x y = if x = y ∧ y ∉ A then 1 else 0 := by
  simp only [killedWeight, avoidsBefore, walkEndpoint, walkWeight, true_and]
  change (∑ _ : PUnit, if x = y ∧ y ∉ A then (1 : ℝ) else 0) = _
  simp

/-- A killed path cannot start in A. -/
theorem killedWeight_of_mem (s : Finset Γ) (μ : Γ → ℝ)
    (A : Set Γ) {x : Γ} (hx : x ∈ A) (n : ℕ) (y : Γ) : killedWeight s μ A n x y = 0 := by
  cases n with
  | zero =>
    rw [killedWeight_zero]
    split_ifs with h
    · exact (h.2 (h.1 ▸ hx)).elim
    · rfl
  | succ n =>
    apply Finset.sum_eq_zero
    intro w _
    simp only [avoidsBefore, hx, not_true_eq_false, false_and, ite_false]

/-- First-step decomposition for the paths avoiding A. -/
theorem killedWeight_succ (s : Finset Γ) (μ : Γ → ℝ)
    (A : Set Γ) {x : Γ} (hx : x ∉ A) (n : ℕ) (y : Γ) :
    killedWeight s μ A (n + 1) x y = ∑ g ∈ s, μ g * killedWeight s μ A n (x * g) y := by
  unfold killedWeight
  rw [← Finset.sum_coe_sort s]
  change (∑ w : s × WalkWord s n,
    if avoidsBefore s A (n + 1) x w ∧ walkEndpoint s (n + 1) x w = y ∧ y ∉ A
    then walkWeight s μ (n + 1) w else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [avoidsBefore, walkEndpoint, walkWeight, hx, not_false_eq_true, true_and]
  split_ifs <;> simp

/-- The Green kernel of the paths avoiding A. -/
def killedGreen (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x y : Γ) : ℝ :=
  ∑' n : ℕ, killedWeight s μ A n x y

theorem killedGreen_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (A : Set Γ) (x y : Γ) : 0 ≤ killedGreen s μ A x y :=
  tsum_nonneg (fun n => killedWeight_nonneg s μ hμ A n x y)

theorem killedGreen_of_mem (s : Finset Γ) (μ : Γ → ℝ)
    (A : Set Γ) {x : Γ} (hx : x ∈ A) (y : Γ) : killedGreen s μ A x y = 0 := by
  simp only [killedGreen, killedWeight_of_mem s μ A hx, tsum_zero]

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ)

include hμ hgap

theorem killedWeight_summable (x y : Γ) : Summable (fun n : ℕ => killedWeight s μ A n x y) := by
  apply (walkGreen_summable s μ hgap x y).of_norm_bounded_eventually_nat
  exact Filter.Eventually.of_forall (fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (killedWeight_nonneg s μ hμ A n x y)]
    exact killedWeight_le_transition s μ hμ A n x y)

theorem killedGreen_le_green (x y : Γ) : killedGreen s μ A x y ≤ walkGreen s μ x y :=
  Summable.tsum_le_tsum (fun n => killedWeight_le_transition s μ hμ A n x y)
    (killedWeight_summable s μ hμ hgap A x y) (walkGreen_summable s μ hgap x y)

/-- The exterior Green equation, with all time-series interchanges justified. -/
theorem killedGreen_first_step {x : Γ} (hx : x ∉ A) (y : Γ) :
    killedGreen s μ A x y = (if x = y then 1 else 0) +
      ∑ g ∈ s, μ g * killedGreen s μ A (x * g) y := by
  have hzero : killedWeight s μ A 0 x y = if x = y then 1 else 0 := by
    rw [killedWeight_zero]
    by_cases hxy : x = y
    · subst y; simp [hx]
    · simp [hxy]
  rw [killedGreen, (killedWeight_summable s μ hμ hgap A x y).tsum_eq_zero_add, hzero]
  simp_rw [killedWeight_succ s μ A hx]
  rw [Summable.tsum_finsetSum (fun g _ =>
    (killedWeight_summable s μ hμ hgap A (x * g) y).mul_left (μ g))]
  simp only [killedGreen, tsum_mul_left]

variable [Countable Γ]

/-- The killed path column is square-integrable. -/
theorem killedGreenColumn_memLp (y : Γ) :
    MemLp (fun x => (killedGreen s μ A x y : ℂ)) 2 Measure.count := by
  apply (Lp.memLp (green (rightMarkov s μ) (countingDelta y))).mono
    (measurable_of_countable _).aestronglyMeasurable
  apply Measure.ae_count_iff.mpr
  intro x
  rw [← walkGreen_eq_coefficient s μ hgap]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (killedGreen_nonneg s μ hμ A x y),
    abs_of_nonneg (walkGreen_nonneg s μ hμ x y)]
  exact killedGreen_le_green s μ hμ hgap A x y

/-- The actual ℓ² column of the killed path kernel. -/
def killedGreenColumn (y : Γ) : GroupL2 Γ :=
  (killedGreenColumn_memLp s μ hμ hgap A y).toLp (fun x => (killedGreen s μ A x y : ℂ))

theorem killedGreenColumn_apply (y x : Γ) :
    killedGreenColumn s μ hμ hgap A y x = (killedGreen s μ A x y : ℂ) :=
  Measure.ae_count_iff.mp (MemLp.coeFn_toLp (killedGreenColumn_memLp s μ hμ hgap A y)) x

theorem killedGreenColumn_boundary (y : Γ) {x : Γ} (hx : x ∈ A) :
    killedGreenColumn s μ hμ hgap A y x = 0 := by
  rw [killedGreenColumn_apply, killedGreen_of_mem s μ A hx, Complex.ofReal_zero]

/-- Its defect under I-P equals δ_y outside A. -/
theorem killedGreenColumn_defect (y : Γ) {x : Γ} (hx : x ∉ A) :
    (killedGreenColumn s μ hμ hgap A y -
      rightMarkov s μ (killedGreenColumn s μ hμ hgap A y)) x = countingDelta y x := by
  rw [counting_sub_apply, rightMarkov_apply, countingDelta_apply]
  simp_rw [killedGreenColumn_apply]
  have h := congrArg Complex.ofReal (killedGreen_first_step s μ hμ hgap A hx y)
  push_cast at h
  by_cases hxy : x = y
  · simpa [hxy] using sub_eq_iff_eq_add.mpr h
  · simpa [hxy] using sub_eq_iff_eq_add.mpr h

end Singularity
