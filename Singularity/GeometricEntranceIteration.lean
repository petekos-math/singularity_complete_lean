import Singularity.FiniteEntranceIteration
import Singularity.GeometricEntranceErrors

/-!
# Geometric conditions sufficient for the finite entrance iteration

The relative detour estimates in both orientations and a summable radius
schedule discharge the error hypotheses of the transfer argument. A finite
sequence of orbit balls and admissible endpoint sets with the stated properties
is constructed in the later CocompactAxisAncona module.
No existence of such a geometric sequence is assumed as an axiom.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A reversed geometric error schedule has total mass at most one half. -/
theorem finite_geometric_errors_le_half (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ n < N, ε n ≤ (1 / 4) * (1 / 2 : ℝ) ^ (N - 1 - n)) :
    ∑ n ∈ Finset.range N, ε n ≤ 1 / 2 := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, (1 / 4) * (1 / 2 : ℝ) ^ (N - 1 - n) :=
      Finset.sum_le_sum (fun n hn => hε n (Finset.mem_range.mp hn))
    _ = (1 / 4) * ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n := by
      rw [← Finset.mul_sum, Finset.sum_range_reflect]
    _ ≤ (1 / 4) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).sum_le_tsum (Finset.range N) (fun _ _ => by positivity)
    _ = 1 / 2 := by rw [tsum_geometric_two]; norm_num

/-- Radii separated backwards by at least log 2 give the required total loss. -/
theorem finite_radius_errors_le_half (N : ℕ) (r : ℕ → ℝ)
    (hr : ∀ n < N, Real.log 4 + (N - 1 - n : ℕ) * Real.log 2 ≤ r n) :
    ∑ n ∈ Finset.range N, Real.exp (-r n) ≤ 1 / 2 := by
  apply finite_geometric_errors_le_half N
  intro n hn
  calc
    _ ≤ Real.exp (-(Real.log 4 + (N - 1 - n : ℕ) * Real.log 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (hr n hn))
    _ = (1 / 4) * (1 / 2 : ℝ) ^ (N - 1 - n) := by
      rw [neg_add, Real.exp_add, ← mul_neg, Real.exp_nat_mul,
        Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4),
        Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

/-- All analytic hypotheses of the finite iteration follow from explicit
ball geometry and a radius schedule. The ball sequence itself is still input. -/
theorem geometric_finite_entrance_iteration (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D B L : ℝ) :
    ∃ R₀ H : ℝ, 0 < R₀ ∧ 0 < H ∧
      ∀ (N : ℕ) (A : ℕ → Finset Γ) (last : ℕ → Bool) (S : ℕ → Set (Γ × Γ))
        (r : ℕ → ℝ) (c : ℕ → Γ) (o : Γ),
      (∀ n < N, R₀ + (N - 1 - n : ℕ) * Real.log 2 ≤ r n) →
      (∀ n < N, (A n : Set Γ) =
        {g : Γ | dist (g • UpperHalfPlane.I) (c n • UpperHalfPlane.I) < r n}) →
      (∀ n < N, ∀ p ∈ S n, ∀ a : A n,
        (if last n then (p.1, (a : Γ)) else ((a : Γ), p.2)) ∈ S (n + 1)) →
      (∀ n < N, ∀ p ∈ S n,
        2 ≤ dist (p.1 • UpperHalfPlane.I) (p.2 • UpperHalfPlane.I) ∧
        dist (p.1 • UpperHalfPlane.I) (p.2 • UpperHalfPlane.I) ≤ B * r n ∧
        dist (p.1 • UpperHalfPlane.I) (c n • UpperHalfPlane.I) +
          dist (p.2 • UpperHalfPlane.I) (c n • UpperHalfPlane.I) -
          dist (p.1 • UpperHalfPlane.I) (p.2 • UpperHalfPlane.I) ≤ D) →
      (∀ p ∈ S N, dist (p.1 • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ L) →
      ∀ p ∈ S 0, walkGreen s μ p.1 p.2 ≤ H * (walkGreen s μ p.1 o * walkGreen s μ o p.2) := by
  obtain ⟨Rmin, herror⟩ := entrancePairRemainder_relative_bound Γ s μ hpos hgen hgap D B 1
  obtain ⟨H, hH, hiterate⟩ := hyperbolic_finite_entrance_iteration Γ s μ hpos hmass hgen hgap L
  let R₀ := max Rmin (Real.log 4) + 1
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith [le_max_right Rmin (Real.log 4)]
  have hbase : Real.log 4 ≤ R₀ := by dsimp [R₀]; linarith [le_max_right Rmin (Real.log 4)]
  have hmin : Rmin ≤ R₀ := by dsimp [R₀]; linarith [le_max_left Rmin (Real.log 4)]
  refine ⟨R₀, H, hR₀, hH, ?_⟩
  intro N A last S r c o hr hA hmove hgeom hterminal
  apply hiterate N A last S (fun n => Real.exp (-r n)) o
    (fun _ _ => (Real.exp_pos _).le) _ hmove _ hterminal
  · apply finite_radius_errors_le_half N r
    intro n hn
    exact (add_le_add hbase le_rfl).trans (hr n hn)
  · intro n hn p hp
    obtain ⟨hd, hdiam, hexcess⟩ := hgeom n hn p hp
    have hrmin : Rmin ≤ r n := by
      have htail : 0 ≤ (N - 1 - n : ℕ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
      linarith [hr n hn]
    simpa only [neg_one_mul] using herror (r n) hrmin (c n) (A n) (last n) p
      (hA n hn) hd hdiam hexcess

end Singularity
