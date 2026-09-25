import Singularity.RelativeGreenEntrance

/-!
# Killed Green lower bounds along interior chains

The initial visit contributes one on the surviving diagonal. Iterating local
row comparisons along a chain therefore gives an exponential lower bound.
-/

noncomputable section
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ]

/-- Killing does not remove the initial visit at a surviving vertex. -/
theorem killedGreen_diag_ge_one (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (x : Γ) (hx : x ∉ A) : 1 ≤ killedGreen s μ A x x := by
  have hh := (killedWeight_summable s μ hμ hgap A x x).le_tsum 0
    (fun n _ => killedWeight_nonneg s μ hμ A n x x)
  simpa [killedWeight_zero, hx, killedGreen] using hh

/-- A finite chain of interior Harnack comparisons gives a positive lower
bound between its endpoints. The chain need not consist of permitted jumps. -/
theorem killedGreen_lower_of_harnack_chain (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (C : ℝ) (hC : 0 < C) (f : ℕ → Γ) (n : ℕ) (hend : f n ∉ A)
    (hlocal : ∀ k < n, ∀ y : Γ, killedGreen s μ A (f (k+1)) y ≤ C * killedGreen s μ A (f k) y) :
    Real.exp (-(n:ℝ)*Real.log C) ≤ killedGreen s μ A (f 0) (f n) := by
  have hb (m : ℕ) (hm : m ≤ n) :
      killedGreen s μ A (f m) (f n) ≤ C^m * killedGreen s μ A (f 0) (f n) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hh := (hlocal m (by omega) (f n)).trans
        (mul_le_mul_of_nonneg_left (ih (by omega)) hC.le)
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hh
  have hh := (killedGreen_diag_ge_one s μ hμ hgap A (f n) hend).trans (hb n le_rfl)
  have he : Real.exp (-(n:ℝ)*Real.log C) = 1/C^n := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hC, one_div]
  rw [he]
  apply (div_le_iff₀ (pow_pos hC n)).mpr
  simpa only [mul_comm] using hh

end Singularity
