import Singularity.ParabolicDisplacement
import Singularity.PeriodicStrip

/-!
# Height bounds on a discrete orbit in parabolic coordinates

Proper discontinuity gives a positive gap between zero and the nonzero
orbit displacements at a fixed basepoint. Conjugating a nontrivial upper
shear by each group element then bounds the height of every orbit point.
No finite generation, finite covolume, or virtual freeness is needed.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The displacement formula for a horizontal translation at any basepoint. -/
theorem upperShearMatrix_dist (u : ℝ) (z : ℍ) :
    dist z (upperShearMatrix u • z) = 2 * Real.arsinh (|u| / (2 * z.im)) := by
  have him : (upperShearMatrix u • z).im = z.im := by
    change (((upperShearMatrix u • z : ℍ) : ℂ)).im = z.im
    rw [upperShearMatrix_smul_coe]
    simp
  rw [UpperHalfPlane.dist_eq, him]
  have hs : Real.sqrt (z.im * z.im) = z.im := by
    simpa only [pow_two] using Real.sqrt_sq z.im_pos.le
  rw [hs]
  simp only [upperShearMatrix_smul_coe, dist_eq_norm]
  rw [show (z : ℂ) - ((z : ℂ) + (u : ℂ)) = -(u : ℂ) by ring,
    norm_neg, Complex.norm_real, Real.norm_eq_abs]

/-- A nontrivial horizontal translation fixes no interior point. -/
theorem upperShearMatrix_smul_ne (u : ℝ) (hu : u ≠ 0) (z : ℍ) :
    upperShearMatrix u • z ≠ z := by
  intro he
  have hh := congrArg (fun w : ℍ => (w : ℂ).re) he
  rw [upperShearMatrix_smul_coe] at hh
  simp only [Complex.add_re, Complex.ofReal_re] at hh
  exact hu (by linarith)

/-- Nonzero orbit displacements in a discrete group have a positive lower bound.
Elements of the finite point stabilizer are explicitly excluded. -/
theorem discrete_orbit_displacement_gap (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : Γ, g • z ≠ z → ε ≤ dist z (g • z) := by
  let S : Finset Γ := (finite_group_vertices_in_compact Γ z (isCompact_closedBall z 1)).toFinset
  have hfin : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ S, g • z ≠ z → ε ≤ dist z (g • z) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a T ha ih =>
      obtain ⟨ε, hε, hT⟩ := ih
      by_cases hz : a • z = z
      · refine ⟨ε, hε, ?_⟩
        intro g hg hg'
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact (hg' hz).elim
        · exact hT g hg hg'
      · refine ⟨min ε (dist z (a • z)), lt_min hε (dist_pos.mpr (Ne.symm hz)), ?_⟩
        intro g hg hg'
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hT g hg hg')
  obtain ⟨ε, hε, hS⟩ := hfin
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro g hg
  by_cases hd : dist z (g • z) ≤ 1
  · have hmem : g ∈ S := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_comm] using hd
    exact (min_le_left _ _).trans (hS g hmem hg)
  · exact (min_le_right _ _).trans (le_of_not_ge hd)

/-- A discrete group containing a nontrivial upper shear has a uniformly
bounded-height orbit at every basepoint. -/
theorem discrete_upperShear_orbit_height_bound (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (u : ℝ) (hu : u ≠ 0) (hmem : upperShearMatrix u ∈ Γ) (z : ℍ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Γ, (g • z).im ≤ C := by
  obtain ⟨ε, hε, hgap⟩ := discrete_orbit_displacement_gap Γ z
  have hs : 0 < Real.sinh (ε / 2) := Real.sinh_pos_iff.mpr (by linarith)
  refine ⟨|u| / (2 * Real.sinh (ε / 2)), div_pos (abs_pos.mpr hu) (by positivity), ?_⟩
  intro g
  let p : Γ := ⟨upperShearMatrix u, hmem⟩
  let a : Γ := g⁻¹ * p * g
  have hact : g • (a • z) = upperShearMatrix u • (g • z) := by
    change (g : SL(2, ℝ)) • (((g : SL(2, ℝ))⁻¹ * upperShearMatrix u * g) • z) = _
    simp only [mul_smul, smul_inv_smul]
    rfl
  have hne : a • z ≠ z := by
    intro hz
    have hh := congrArg (fun w : ℍ => g • w) hz
    rw [hact] at hh
    exact upperShearMatrix_smul_ne u hu (g • z) hh
  have hd : ε ≤ dist (g • z) (upperShearMatrix u • (g • z)) := by
    have hh := hgap a hne
    rw [← dist_smul (g : SL(2, ℝ)) z (a • z)] at hh
    change ε ≤ dist (g • z) (g • (a • z)) at hh
    rwa [hact] at hh
  rw [upperShearMatrix_dist] at hd
  have hsh : Real.sinh (ε / 2) ≤ |u| / (2 * (g • z).im) := by
    rw [← Real.sinh_arsinh (|u| / (2 * (g • z).im))]
    apply Real.sinh_le_sinh.mpr
    linarith
  have hm := (le_div_iff₀ (show 0 < 2 * (g • z).im by positivity)).mp hsh
  apply (le_div_iff₀ (show 0 < 2 * Real.sinh (ε / 2) by positivity)).mpr
  nlinarith

end Singularity
