import Singularity.HyperbolicTraceSquare
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Hyperbolic traces from a shrinking lower row

If the lower row of a sequence in a subgroup tends to zero, bounded traces for
that sequence and for its products with a fixed matrix force the latter matrix
to have zero lower-left entry. Thus any element moving infinity yields an element
of hyperbolic trace.
-/

noncomputable section
open Filter
open scoped Topology MatrixGroups

namespace Singularity

/-- A uniformly bounded real factor times a sequence tending to zero tends to zero. -/
theorem bounded_mul_tendsto_zero (f h : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n, |f n| ≤ C) (hh : Tendsto h atTop (nhds 0)) :
    Tendsto (fun n => f n * h n) atTop (nhds 0) := by
  apply squeeze_zero_norm (fun n => ?_) (by simpa using hh.norm.const_mul C)
  rw [norm_mul, Real.norm_eq_abs (f n)]
  exact mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)

/-- A small lower row and an element not fixing infinity force a hyperbolic trace. -/
theorem exists_hyperbolic_of_small_lower_row (Γ : Subgroup SL(2, ℝ))
    (g : ℕ → Γ)
    (hc : Tendsto (fun n => (g n : SL(2, ℝ)) 1 0) atTop (nhds 0))
    (hd : Tendsto (fun n => (g n : SL(2, ℝ)) 1 1) atTop (nhds 0))
    (b : Γ) (hb : (b : SL(2, ℝ)) 1 0 ≠ 0) :
    ∃ a : Γ, 2 < |(a : SL(2, ℝ)) 0 0 + (a : SL(2, ℝ)) 1 1| := by
  by_contra h
  push Not at h
  let T : ℕ → ℝ := fun n => (g n : SL(2, ℝ)) 0 0 + (g n : SL(2, ℝ)) 1 1
  let U : ℕ → ℝ := fun n => ((g n * b : Γ) : SL(2, ℝ)) 0 0 + ((g n * b : Γ) : SL(2, ℝ)) 1 1
  have hTc := bounded_mul_tendsto_zero T _ 2 (fun n => h (g n)) hc
  have hTd := bounded_mul_tendsto_zero T _ 2 (fun n => h (g n)) hd
  have hUc := bounded_mul_tendsto_zero U _ 2 (fun n => h (g n * b)) hc
  have hac : Tendsto (fun n => (g n : SL(2, ℝ)) 0 0 * (g n : SL(2, ℝ)) 1 0)
      atTop (nhds 0) := by
    have ht := hTc.sub (hd.mul hc)
    convert ht using 1
    · funext n; dsimp [T]; ring
    · simp
  have had : Tendsto (fun n => (g n : SL(2, ℝ)) 0 0 * (g n : SL(2, ℝ)) 1 1)
      atTop (nhds 0) := by
    have ht := hTd.sub (hd.mul hd)
    convert ht using 1
    · funext n; dsimp [T]; ring
    · simp
  have ht := ((((hac.const_mul ((b : SL(2, ℝ)) 0 0)).add
    (had.const_mul ((b : SL(2, ℝ)) 1 0))).add
    ((hc.mul hc).const_mul ((b : SL(2, ℝ)) 0 1))).add
    ((hd.mul hc).const_mul ((b : SL(2, ℝ)) 1 1))).sub hUc
  have hconst : Tendsto (fun _ : ℕ => (b : SL(2, ℝ)) 1 0) atTop (nhds 0) := by
    convert ht using 1
    · funext n
      have hdet : (g n : SL(2, ℝ)) 0 0 * (g n : SL(2, ℝ)) 1 1 -
          (g n : SL(2, ℝ)) 0 1 * (g n : SL(2, ℝ)) 1 0 = 1 := by
        simpa only [Matrix.det_fin_two] using (g n : SL(2, ℝ)).property
      dsimp [U]
      simp only [Matrix.mul_apply,
        Fin.sum_univ_two]
      nlinarith [congrArg (fun x : ℝ => (b : SL(2, ℝ)) 1 0 * x) hdet]
    · simp
  exact hb (tendsto_nhds_unique tendsto_const_nhds hconst)

end Singularity
