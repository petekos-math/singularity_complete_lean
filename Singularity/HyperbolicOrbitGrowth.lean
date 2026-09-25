import Singularity.HyperbolicGrid
import Singularity.PeriodicStrip

/-!
# Exponential orbit growth for a discrete Fuchsian subgroup

Proper discontinuity gives finitely many group vertices in each compact ball,
including multiplicities from stabilizers. Each grid fiber injects by translation
into the radius-two group ball, giving a uniform exponential cardinality bound.
No cocompactness or Green comparison is used.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]

/-- All group vertices whose orbit points lie in the closed radius-R ball about i. -/
def hyperbolicOrbitBall (R : ℝ) : Finset Γ :=
  (finite_group_vertices_in_compact Γ UpperHalfPlane.I
    (isCompact_closedBall UpperHalfPlane.I R)).toFinset

/-- Membership retains group multiplicity, even if the base point has a stabilizer. -/
theorem mem_hyperbolicOrbitBall (R : ℝ) (g : Γ) :
    g ∈ hyperbolicOrbitBall Γ R ↔ dist (g • UpperHalfPlane.I) UpperHalfPlane.I ≤ R := by
  simp [hyperbolicOrbitBall, Metric.mem_closedBall]

/-- A grid fiber injects into the fixed radius-two ball by a group translation. -/
theorem hyperbolicOrbitGrid_fiber_card (R : ℝ) (c : ℤ × ℤ) :
    ((hyperbolicOrbitBall Γ R).filter
      (fun g => hyperbolicGrid R (g • UpperHalfPlane.I) = c)).card ≤
        (hyperbolicOrbitBall Γ 2).card := by
  classical
  let F := (hyperbolicOrbitBall Γ R).filter
    (fun g => hyperbolicGrid R (g • UpperHalfPlane.I) = c)
  change F.card ≤ _
  by_cases hF : F.Nonempty
  · obtain ⟨g, hg⟩ := hF
    obtain ⟨hgb, hgc⟩ := Finset.mem_filter.mp hg
    apply Finset.card_le_card_of_injOn (fun h : Γ => g⁻¹ * h)
    · intro h hh
      obtain ⟨hhb, hhc⟩ := Finset.mem_filter.mp hh
      change g⁻¹ * h ∈ hyperbolicOrbitBall Γ 2
      rw [mem_hyperbolicOrbitBall]
      have hd : dist ((g⁻¹ * h) • UpperHalfPlane.I) UpperHalfPlane.I =
          dist (h • UpperHalfPlane.I) (g • UpperHalfPlane.I) := by
        rw [← dist_smul (g : SL(2, ℝ))]
        change dist (g • ((g⁻¹ * h) • UpperHalfPlane.I)) (g • UpperHalfPlane.I) = _
        rw [← mul_smul, mul_inv_cancel_left]
      rw [hd]
      exact hyperbolicGrid_diameter ((mem_hyperbolicOrbitBall Γ R h).mp hhb)
        ((mem_hyperbolicOrbitBall Γ R g).mp hgb) (hhc.trans hgc.symm)
    · intro a _ b _ he
      exact mul_left_cancel he
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.card_empty, Nat.zero_le]

/-- A uniform exponential bound on group vertices in hyperbolic balls. -/
theorem hyperbolicOrbitBall_card {R : ℝ} (hR : 0 ≤ R) :
    ((hyperbolicOrbitBall Γ R).card : ℝ) ≤
      (49 * (hyperbolicOrbitBall Γ 2).card) * Real.exp (4 * R) := by
  have hmap : (hyperbolicOrbitBall Γ R : Set Γ).MapsTo
      (fun g => hyperbolicGrid R (g • UpperHalfPlane.I))
      (↑((hyperbolicGridRange R) ×ˢ (hyperbolicGridRange R) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    intro g hg
    exact hyperbolicGrid_mem ((mem_hyperbolicOrbitBall Γ R g).mp hg)
  have hcard : (hyperbolicOrbitBall Γ R).card ≤
      ((hyperbolicGridRange R) ×ˢ (hyperbolicGridRange R)).card *
        (hyperbolicOrbitBall Γ 2).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    exact (Finset.sum_le_sum (fun c _ => hyperbolicOrbitGrid_fiber_card Γ R c)).trans_eq
      (by simp)
  have hc : ((hyperbolicOrbitBall Γ R).card : ℝ) ≤
      (((hyperbolicGridRange R) ×ˢ (hyperbolicGridRange R)).card : ℝ) *
        (hyperbolicOrbitBall Γ 2).card := by exact_mod_cast hcard
  apply hc.trans
  have hg := mul_le_mul_of_nonneg_right (hyperbolicGrid_card hR)
    (Nat.cast_nonneg (hyperbolicOrbitBall Γ 2).card : (0 : ℝ) ≤ _)
  convert hg using 1; ring

end Singularity
