import Singularity.ExponentialLattice
import Singularity.GeometricDetour

/-!
# Exponential bounds along finite quasigeodesics

A nearest vertex and a linear lower distance bound give exponential decay in
the index away from that vertex. Summing this decay bounds the entire movement
in the Cayley disk independently of the length of the path.
-/

noncomputable section
open scoped Classical BigOperators UpperHalfPlane

namespace Singularity

/-- A finite interval of integer translates satisfies the lattice envelope bound. -/
theorem sum_exp_nat_distance_le {τ : ℝ} (hτ : 0 < τ) (m N : ℕ) :
    ∑ k ∈ Finset.range N, Real.exp (-τ * |(k : ℝ) - (m : ℝ)|) ≤
      latticeEnvelopeBound τ := by
  have h := sum_exp_lattice_le hτ ((m : ℝ) * τ)
    ((Finset.range N).image (fun k : ℕ => (k : ℤ)))
  rw [Finset.sum_image (by intros a _ b _ hab; exact Int.ofNat_injective hab)] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp only [Int.cast_natCast]
  rw [show (m : ℝ) * τ - (k : ℝ) * τ = -((k : ℝ) - m) * τ by ring,
    abs_mul, abs_neg, abs_of_pos hτ]
  ring

/-- Distance from a nearest vertex has both a uniform and an index-dependent
lower bound; averaging them produces a summable envelope. -/
theorem nearest_vertex_exp_bound {X : Type*} [PseudoMetricSpace X]
    (p : ℕ → X) (o : X) (a b : ℝ) (m k : ℕ)
    (hmin : dist o (p m) ≤ dist o (p k))
    (hlower : a * |(k : ℝ) - (m : ℝ)| - b ≤ dist (p k) (p m)) :
    Real.exp (-dist o (p k)) ≤
      Real.exp (-dist o (p m) / 2 + b / 4) *
        Real.exp (-(a / 4) * |(k : ℝ) - (m : ℝ)|) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht := dist_triangle (p k) o (p m)
  rw [dist_comm (p k) o] at ht
  linarith

/-- The distance between the endpoints is at most the sum of the successive
Cayley movements. -/
theorem cayley_chain_bound (p : ℕ → ℍ) (N : ℕ) (L : ℝ)
    (hstep : ∀ k < N, dist (p k) (p (k + 1)) ≤ L) :
    dist (halfPlaneCayley (p 0)) (halfPlaneCayley (p N)) ≤
      4 * Real.exp L * ∑ k ∈ Finset.range N, Real.exp (-dist UpperHalfPlane.I (p k)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      _ ≤ dist (halfPlaneCayley (p 0)) (halfPlaneCayley (p N)) +
          dist (halfPlaneCayley (p N)) (halfPlaneCayley (p (N + 1))) := dist_triangle _ _ _
      _ ≤ 4 * Real.exp L * (∑ k ∈ Finset.range N, Real.exp (-dist UpperHalfPlane.I (p k))) +
          4 * Real.exp L * Real.exp (-dist UpperHalfPlane.I (p N)) := by
        apply add_le_add (ih (fun k hk => hstep k (by omega)))
        simpa only [dist_comm] using halfPlaneCayley_dist_le (p N) (p (N + 1)) L (hstep N (by omega))
      _ = _ := by rw [Finset.sum_range_succ, mul_add]

/-- A linearly separated chain has exponentially small total Cayley movement
when all of its vertices lie far from the center. -/
theorem cayley_quasigeodesic_envelope (p : ℕ → ℍ) (N m : ℕ) (a b L : ℝ)
    (ha : 0 < a)
    (hstep : ∀ k < N, dist (p k) (p (k + 1)) ≤ L)
    (hmin : ∀ k < N, dist UpperHalfPlane.I (p m) ≤ dist UpperHalfPlane.I (p k))
    (hlower : ∀ k < N, a * |(k : ℝ) - (m : ℝ)| - b ≤ dist (p k) (p m)) :
    dist (halfPlaneCayley (p 0)) (halfPlaneCayley (p N)) ≤
      4 * Real.exp L * (Real.exp (-dist UpperHalfPlane.I (p m) / 2 + b / 4) *
        latticeEnvelopeBound (a / 4)) := by
  apply (cayley_chain_bound p N L hstep).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ k ∈ Finset.range N, Real.exp (-dist UpperHalfPlane.I (p m) / 2 + b / 4) *
        Real.exp (-(a / 4) * |(k : ℝ) - (m : ℝ)|) := by
      apply Finset.sum_le_sum
      intro k hk
      exact nearest_vertex_exp_bound p UpperHalfPlane.I a b m k
        (hmin k (Finset.mem_range.mp hk)) (hlower k (Finset.mem_range.mp hk))
    _ = Real.exp (-dist UpperHalfPlane.I (p m) / 2 + b / 4) *
        ∑ k ∈ Finset.range N, Real.exp (-(a / 4) * |(k : ℝ) - (m : ℝ)|) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_exp_nat_distance_le (by positivity) m N)
      (Real.exp_nonneg _)

end Singularity
