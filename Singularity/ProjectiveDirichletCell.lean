import Singularity.ProjectiveOrbitSubsequences
import Singularity.QuasiconvexFullBoundary

/-!
# Closed Dirichlet cells for discrete projective groups

The cell consists of points at least as close to its centre as to any other
point of the centre's orbit. Stabilizers are allowed: no uniqueness of the
orbit representative or disjointness of closed translates is asserted.
Properness supplies a nearest orbit point and hence a translate in the cell.
On each bounded ball, only finitely many orbit points impose constraints.
-/

noncomputable section
open Set
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- The closed metric Dirichlet cell with centre `z`. -/
def projectiveDirichletCell (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) : Set ℍ :=
  {w | ∀ g : Γ, dist w z ≤ dist w (g • z)}

theorem projectiveDirichletCell_center (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    z ∈ projectiveDirichletCell Γ z := by
  intro g
  simpa using (dist_nonneg : 0 ≤ dist z (g • z))

theorem isClosed_projectiveDirichletCell (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    IsClosed (projectiveDirichletCell Γ z) := by
  have he : projectiveDirichletCell Γ z =
      ⋂ g : Γ, {w : ℍ | dist w z ≤ dist w (g • z)} := by
    ext w
    simp only [projectiveDirichletCell, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter (fun g : Γ =>
    isClosed_le (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))

/-- A discrete orbit has a nearest point to every interior point. -/
theorem exists_nearest_projective_orbit_point
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z w : ℍ) :
    ∃ g : Γ, ∀ h : Γ, dist w (g • z) ≤ dist w (h • z) := by
  have hfin := finite_projective_group_vertices_in_compact Γ z
    (isCompact_closedBall w (dist w z))
  have hmem : (1 : Γ) ∈ hfin.toFinset := by
    apply hfin.mem_toFinset.mpr
    change dist ((1 : Γ) • z) w ≤ dist w z
    simp only [one_smul, dist_comm]
    exact le_rfl
  obtain ⟨g, hg, hmin⟩ := hfin.toFinset.exists_min_image
    (fun a : Γ => dist w (a • z)) ⟨1, hmem⟩
  refine ⟨g, fun h => ?_⟩
  by_cases hh : h ∈ hfin.toFinset
  · exact hmin h hh
  · have hh' : dist w z < dist w (h • z) := by
      apply lt_of_not_ge
      intro hd
      apply hh
      apply hfin.mem_toFinset.mpr
      exact (dist_comm _ _).trans_le hd
    have hg' := hmin 1 hmem
    simp only [one_smul] at hg'
    exact hg'.trans hh'.le

/-- Moving a nearest orbit point back to the centre moves the given point
into the closed cell. -/
theorem exists_smul_mem_projectiveDirichletCell
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z w : ℍ) :
    ∃ g : Γ, g • w ∈ projectiveDirichletCell Γ z := by
  obtain ⟨g, hg⟩ := exists_nearest_projective_orbit_point Γ z w
  refine ⟨g⁻¹, fun h => ?_⟩
  have h1 := projective_dist_smul (g : PSL(2, ℝ)) (g⁻¹ • w) z
  have h2 := projective_dist_smul (g : PSL(2, ℝ)) (g⁻¹ • w) (h • z)
  change dist (g • (g⁻¹ • w)) (g • z) = _ at h1
  change dist (g • (g⁻¹ • w)) (g • (h • z)) = _ at h2
  rw [smul_inv_smul] at h1 h2
  rw [← h1, ← h2, ← mul_smul]
  exact hg (g * h)

/-- A point farther than twice the radius from the centre cannot cut the
Dirichlet cell inside that radius. -/
theorem projectiveDirichletCell_constraint_of_far
    (Γ : Subgroup PSL(2, ℝ)) (z w : ℍ) (R : ℝ) (g : Γ)
    (hw : dist w z ≤ R) (hg : 2 * R < dist z (g • z)) :
    dist w z < dist w (g • z) := by
  have ht := dist_triangle z w (g • z)
  rw [dist_comm z w] at ht
  linarith

/-- On a fixed closed ball the cell is described by finitely many of its
actual orbit-distance inequalities. The finite set may depend on the radius. -/
theorem projectiveDirichletCell_finite_constraints_on_ball
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (R : ℝ) :
    ∃ F : Finset Γ, ∀ w ∈ Metric.closedBall z R,
      w ∈ projectiveDirichletCell Γ z ↔
        ∀ g ∈ F, dist w z ≤ dist w (g • z) := by
  have hf := finite_projective_group_vertices_in_compact Γ z
    (isCompact_closedBall z (2 * R))
  refine ⟨hf.toFinset, fun w hw => ⟨fun h g _ => h g, fun h g => ?_⟩⟩
  by_cases hg : g ∈ hf.toFinset
  · exact h g hg
  · have hg' : 2 * R < dist z (g • z) := by
      apply lt_of_not_ge
      intro hd
      apply hg
      apply hf.mem_toFinset.mpr
      exact (dist_comm _ _).trans_le hd
    exact (projectiveDirichletCell_constraint_of_far Γ z w R g hw hg').le

/-- A bound on the cell is exactly a uniform bound on distance to the orbit. -/
theorem projectiveDirichletCell_subset_ball_iff_cover
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (R : ℝ) :
    projectiveDirichletCell Γ z ⊆ Metric.closedBall z R ↔
      ∀ w : ℍ, ∃ g : Γ, dist w (g • z) ≤ R := by
  constructor
  · intro h w
    obtain ⟨g, hg⟩ := exists_smul_mem_projectiveDirichletCell Γ z w
    refine ⟨g⁻¹, ?_⟩
    have hd := h hg
    have he := projective_dist_smul (g : PSL(2, ℝ)) w (g⁻¹ • z)
    change dist (g • w) (g • (g⁻¹ • z)) = _ at he
    rw [smul_inv_smul] at he
    change dist (g • w) z ≤ R at hd
    rwa [he] at hd
  · intro h w hw
    obtain ⟨g, hg⟩ := h w
    exact (hw g).trans hg

/-- A bounded closed Dirichlet cell supplies a compact hyperbolic quotient. -/
theorem projective_cocompact_of_bounded_dirichletCell
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] (z : ℍ) (R : ℝ)
    (h : projectiveDirichletCell Γ z ⊆ Metric.closedBall z R) :
    CompactSpace (Quotient (MulAction.orbitRel Γ ℍ)) :=
  projective_cocompact_of_uniform_orbit_cover Γ z R
    ((projectiveDirichletCell_subset_ball_iff_cover Γ z R).mp h)

end Singularity
