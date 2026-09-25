import Singularity.ProjectiveCuspStrips
import Singularity.FiniteExitEnlargement

/-!
# Finite exit sets for half-planes with parabolic endpoints

The chart strip is finite. Adding its one-step predecessors ensures that
every allowed jump leaving the negative half-plane starts in the finite exit
set, as required by the trapping-region argument for actual walk paths.
-/

noncomputable section
open Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- The negative side of a chart with two parabolic endpoints admits a finite
outgoing exit set for every finite jump support. -/
theorem projective_cusp_chart_finite_exit_set
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (s : Finset Γ)
    (g h : Γ) (hg : ProjectiveParabolic (g : PSL(2, ℝ)))
    (hh : ProjectiveParabolic (h : PSL(2, ℝ)))
    (p q : OnePoint ℝ) (hgp : g • p = p) (hhq : h • q = q)
    (B : SL(2, ℝ)) (hBp : B • (∞ : OnePoint ℝ) = p)
    (hBq : B • ((0 : ℝ) : OnePoint ℝ) = q) :
    ∃ T : Finset Γ, ∀ v : Γ, (B⁻¹ • (v • z)).re < 0 → v ∉ (T : Set Γ) →
      ∀ t ∈ s, (B⁻¹ • ((v * t) • z)).re < 0 := by
  let L := ∑ t ∈ s, dist z (t • z)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => dist_nonneg)
  have hfinite := finite_projective_cusp_strip_in_chart Γ z g h hg hh p q hgp hhq B hBp hBq
    (jumpStripRadius_pos hL).le
  let A : Finset Γ := hfinite.toFinset
  obtain ⟨T, _, hT⟩ := exists_finite_exit_enlargement s A
    {v : Γ | (B⁻¹ • (v • z)).re < 0} (by
      intro v hv t ht hvt hneg
      have hvout : B⁻¹ • (v • z) ∉ axisRatioStrip (jumpStripRadius L) := by
        simpa only [A, Set.Finite.coe_toFinset, mem_ofPred_eq] using hv
      have hvtout : B⁻¹ • ((v * t) • z) ∉ axisRatioStrip (jumpStripRadius L) := by
        simpa only [A, Set.Finite.coe_toFinset, mem_ofPred_eq] using hvt
      apply bounded_jump_preserves_negative_side hL _ _ ?_ hvout hvtout hneg
      rw [dist_smul, mul_smul]
      change dist ((v : PSL(2, ℝ)) • z) ((v : PSL(2, ℝ)) • (t • z)) ≤ L
      rw [projective_dist_smul]
      change dist z (t • z) ≤ ∑ a ∈ s, dist z (a • z)
      exact Finset.single_le_sum (f := fun a : Γ => dist z (a • z))
        (fun _ _ => dist_nonneg) ht)
  exact ⟨T, hT⟩

end Singularity
