import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A finite shrinking-interval schedule

At each step halve the longer side of an interval containing zero. The total
length contracts by at least a factor 3/4. Stopping at a fixed positive length
therefore gives a finite schedule, with a uniform backwards spacing of radii.
-/

noncomputable section
namespace Singularity

/-- Halve the longer of the nonnegative left and right lengths. -/
def axisIntervalStep (p : ℝ × ℝ) : ℝ × ℝ :=
  if p.2 ≤ p.1 then (p.1 / 2, p.2) else (p.1, p.2 / 2)

/-- The new endpoint, expressed as a signed axis parameter. -/
def axisIntervalCut (p : ℝ × ℝ) : ℝ :=
  if p.2 ≤ p.1 then -p.1 / 2 else p.2 / 2

/-- True means replace the right endpoint, using last entry. -/
def axisIntervalLast (p : ℝ × ℝ) : Bool :=
  if p.2 ≤ p.1 then false else true

/-- The interval lengths after n steps. -/
def axisInterval (l r : ℝ) : ℕ → ℝ × ℝ
  | 0 => (l, r)
  | n + 1 => axisIntervalStep (axisInterval l r n)

theorem axisIntervalStep_nonneg (p : ℝ × ℝ) (hl : 0 ≤ p.1) (hr : 0 ≤ p.2) :
    0 ≤ (axisIntervalStep p).1 ∧ 0 ≤ (axisIntervalStep p).2 := by
  unfold axisIntervalStep
  split <;> dsimp <;> constructor <;> positivity

theorem axisInterval_nonneg (l r : ℝ) (hl : 0 ≤ l) (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ (axisInterval l r n).1 ∧ 0 ≤ (axisInterval l r n).2 := by
  induction n with
  | zero => exact ⟨hl, hr⟩
  | succ n ih => exact axisIntervalStep_nonneg _ ih.1 ih.2

theorem axisIntervalStep_length_bounds (p : ℝ × ℝ) (hl : 0 ≤ p.1) (hr : 0 ≤ p.2) :
    (p.1 + p.2) / 2 ≤ (axisIntervalStep p).1 + (axisIntervalStep p).2 ∧
    (axisIntervalStep p).1 + (axisIntervalStep p).2 ≤ (3 / 4 : ℝ) * (p.1 + p.2) := by
  unfold axisIntervalStep
  split <;> dsimp <;> constructor <;> linarith

theorem axisInterval_length_le (l r : ℝ) (hl : 0 ≤ l) (hr : 0 ≤ r) (n : ℕ) :
    (axisInterval l r n).1 + (axisInterval l r n).2 ≤ (3 / 4 : ℝ)^n * (l + r) := by
  induction n with
  | zero => simp [axisInterval]
  | succ n ih =>
    obtain ⟨hnl, hnr⟩ := axisInterval_nonneg l r hl hr n
    have hstep := (axisIntervalStep_length_bounds (axisInterval l r n) hnl hnr).2
    change (axisIntervalStep _).1 + (axisIntervalStep _).2 ≤ _
    calc
      _ ≤ (3 / 4 : ℝ) * ((axisInterval l r n).1 + (axisInterval l r n).2) := hstep
      _ ≤ (3 / 4 : ℝ) * ((3 / 4 : ℝ)^n * (l + r)) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- Stop on first reaching a prescribed positive total length. -/
theorem exists_axisInterval_stop (l r T : ℝ) (hl : 0 ≤ l) (hr : 0 ≤ r) (hT : 0 < T) :
    ∃ N : ℕ, (axisInterval l r N).1 + (axisInterval l r N).2 ≤ T ∧
      ∀ n < N, T < (axisInterval l r n).1 + (axisInterval l r n).2 := by
  have hex : ∃ n : ℕ, (axisInterval l r n).1 + (axisInterval l r n).2 ≤ T := by
    have hlim : Filter.Tendsto (fun n : ℕ => (3 / 4 : ℝ)^n * (l + r)) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num : (3 / 4 : ℝ) < 1)).mul_const (l + r)
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hT)).exists
    exact ⟨n, (axisInterval_length_le l r hl hr n).trans hn.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro n hn
  exact lt_of_not_ge (Nat.find_min hex hn)

/-- A contracting positive length schedule has a uniformly spaced backwards
radius schedule before the stopping time. -/
theorem axisInterval_radius_schedule (l r T R δ : ℝ) (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hR : 400 * R ≤ T) (hδ : 1600 * δ ≤ T) (N : ℕ)
    (hbefore : ∀ n < N, T < (axisInterval l r n).1 + (axisInterval l r n).2) :
    ∀ n < N, R + (N - 1 - n : ℕ) * δ ≤
      ((axisInterval l r n).1 + (axisInterval l r n).2) / 400 := by
  have hbase : ∀ n < N, R ≤ ((axisInterval l r n).1 + (axisInterval l r n).2) / 400 := by
    intro n hn
    linarith [hbefore n hn]
  have hdiff : ∀ n < N, δ +
      ((axisInterval l r (n+1)).1 + (axisInterval l r (n+1)).2) / 400 ≤
      ((axisInterval l r n).1 + (axisInterval l r n).2) / 400 := by
    intro n hn
    obtain ⟨hnl, hnr⟩ := axisInterval_nonneg l r hl hr n
    have hs := (axisIntervalStep_length_bounds (axisInterval l r n) hnl hnr).2
    change (axisInterval l r (n+1)).1 + (axisInterval l r (n+1)).2 ≤ _ at hs
    linarith [hbefore n hn]
  intro n hn
  have hback : ∀ k : ℕ, ∀ n : ℕ, n + k + 1 = N →
      R + (k : ℝ) * δ ≤ ((axisInterval l r n).1 + (axisInterval l r n).2) / 400 := by
    intro k
    induction k with
    | zero =>
      intro n heq
      simpa using hbase n (by omega)
    | succ k ih =>
      intro n heq
      have hh := ih (n+1) (by omega)
      have hd := hdiff n (by omega)
      rw [Nat.cast_succ]
      linarith
  exact hback (N-1-n) n (by omega)

end Singularity
