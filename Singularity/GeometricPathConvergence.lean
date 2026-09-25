import Singularity.CayleyCompactification
import Singularity.CompactWalkLimit
import Singularity.GeometricStrip
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Full path convergence from summable radial decay

Bounded hyperbolic increments and summability of exp(-distance from i) force
Cauchy convergence of the disk coordinates, hence full convergence in the
compact sphere. Eventual linear escape supplies that summability. The actual
finite-support walk has the required bounded increments.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Summable radial decay and bounded hyperbolic increments make disk positions Cauchy. -/
theorem cayley_cauchySeq_of_summable_escape (z : ℕ → ℍ) (L : ℝ)
    (hjump : ∀ n, dist (z n) (z (n + 1)) ≤ L)
    (hs : Summable (fun n => Real.exp (-dist (z n) UpperHalfPlane.I))) :
    CauchySeq (fun n => halfPlaneCayley (z n)) :=
  cauchySeq_of_dist_le_of_summable
    (fun n => (4 * Real.exp L) * Real.exp (-dist (z n) UpperHalfPlane.I))
    (fun n => halfPlaneCayley_dist_le (z n) (z (n + 1)) L (hjump n))
    (hs.mul_left (4 * Real.exp L))

/-- The full orbit path converges in the compact sphere under summable radial decay. -/
theorem compact_tendsto_of_summable_escape (z : ℕ → ℍ) (L : ℝ)
    (hjump : ∀ n, dist (z n) (z (n + 1)) ≤ L)
    (hs : Summable (fun n => Real.exp (-dist (z n) UpperHalfPlane.I))) :
    ∃ p : OnePoint ℂ, Tendsto (fun n => hyperbolicCompactEmbedding (z n)) atTop (nhds p) := by
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete
    (cayley_cauchySeq_of_summable_escape z L hjump hs)
  exact ⟨cayleyCompactHomeomorph.symm (q : OnePoint ℂ), cayley_tendsto_compact hq⟩

/-- Eventual positive linear escape makes the exponential radial weights summable. -/
theorem summable_radial_of_linear_escape (z : ℕ → ℍ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hescape : ∀ᶠ (n : ℕ) in atTop, a * (n : ℝ) - b ≤ dist (z n) UpperHalfPlane.I) :
    Summable (fun n => Real.exp (-dist (z n) UpperHalfPlane.I)) := by
  have hg := (summable_geometric_of_lt_one (Real.exp_pos (-a)).le
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha))).mul_left (Real.exp b)
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [hescape] with n hn
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul,
    ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Bounded jumps and eventual positive linear escape imply full compact convergence. -/
theorem compact_tendsto_of_linear_escape (z : ℕ → ℍ) (L : ℝ)
    (hjump : ∀ n, dist (z n) (z (n + 1)) ≤ L) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hescape : ∀ᶠ (n : ℕ) in atTop, a * (n : ℝ) - b ≤ dist (z n) UpperHalfPlane.I) :
    ∃ p : OnePoint ℂ, Tendsto (fun n => hyperbolicCompactEmbedding (z n)) atTop (nhds p) :=
  compact_tendsto_of_summable_escape z L hjump (summable_radial_of_linear_escape z ha b hescape)

/-- The final jump is read from the time-n coordinate of the infinite sample. -/
theorem walkPosition_last_step {Γ : Type*} [Group Γ] (s : Finset Γ)
    (x : Γ) (n : ℕ) (ω : ℕ → s) :
    walkPosition s x (n + 1) ω = walkPosition s x n ω * (ω n : Γ) := by
  rw [walkPosition_add]
  simp only [walkPosition_succ, walkPosition_zero, one_mul, Nat.zero_add]

/-- All actual sample paths have a uniform hyperbolic jump bound from finite support. -/
theorem walkPosition_hyperbolic_jump_bound (Γ : Subgroup SL(2, ℝ))
    (s : Finset Γ) (z : ℍ) (x : Γ) (ω : ℕ → s) (n : ℕ) :
    dist (walkPosition s x n ω • z) (walkPosition s x (n + 1) ω • z) ≤
      finiteJumpLengthBound Γ z s := by
  rw [walkPosition_last_step, mul_smul]
  change dist (((walkPosition s x n ω : Γ) : SL(2, ℝ)) • z)
    (((walkPosition s x n ω : Γ) : SL(2, ℝ)) • ((ω n : Γ) • z)) ≤ _
  rw [dist_smul]
  exact dist_le_finiteJumpLengthBound Γ z s (ω n).property

/-- Almost-sure summable radial decay gives actual almost-sure full geometric convergence. -/
theorem walk_ae_compact_convergence_of_summable_escape (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (x : Γ) (z : ℍ)
    (hs : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Summable (fun n => Real.exp (-dist (walkPosition s x n ω • z) UpperHalfPlane.I))) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      ∃ p : OnePoint ℂ, Tendsto
        (fun n => hyperbolicCompactEmbedding (walkPosition s x n ω • z)) atTop (nhds p) := by
  filter_upwards [hs] with ω hω
  exact compact_tendsto_of_summable_escape _ (finiteJumpLengthBound Γ z s)
    (walkPosition_hyperbolic_jump_bound Γ s z x ω) hω

end Singularity
