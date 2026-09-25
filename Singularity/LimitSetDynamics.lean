import Singularity.FuchsianLimitSet
import Singularity.VisualPoissonComparison
import Mathlib.Topology.Sequences

/-!
# Invariance of the ideal limit set and its visual mass along an orbit

The limit set is defined by the actual compactified orbit closure. Its
invariance is proved by transporting convergent orbit sequences, and covariance
of the Poisson measures makes its visual mass constant along each orbit.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- A point of the ideal orbit limit set is approached by an actual orbit sequence. -/
theorem mem_projectiveOrbitLimitSet_iff_sequence (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (p : OnePoint ℝ) :
    p ∈ projectiveOrbitLimitSet Γ z ↔ ∃ g : ℕ → Γ,
      Tendsto (fun n => hyperbolicCompactEmbedding (g n • z)) atTop (𝓝 (compactBoundaryEmbedding p)) := by
  constructor
  · intro hp
    obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.mp hp
    choose g hg using hx
    exact ⟨g, by simpa only [hg] using hlim⟩
  · rintro ⟨g, hg⟩
    exact mem_projectiveOrbitLimitSet_of_tendsto Γ z g p hg

/-- The ideal limit set is preserved by the group action. -/
theorem projectiveOrbitLimitSet_smul_mem (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (g : Γ)
    (p : OnePoint ℝ) (hp : p ∈ projectiveOrbitLimitSet Γ z) :
    g • p ∈ projectiveOrbitLimitSet Γ z := by
  obtain ⟨x, hx⟩ := (mem_projectiveOrbitLimitSet_iff_sequence Γ z p).mp hp
  obtain ⟨a, ha⟩ := slTwoProjective_surjective (g : PSL(2, ℝ))
  have hlim := (continuous_const_smul a).continuousAt.tendsto.comp hx
  have hgeo (w : ℍ) : a • w = g • w := by
    rw [← slTwoProjective_smul_hyperbolic, ha]
    rfl
  have hb : a • compactBoundaryEmbedding p = compactBoundaryEmbedding (g • p) := by
    rw [← compactBoundaryEmbedding_smul, ← slTwoProjective_smul_boundary, ha]
    rfl
  apply mem_projectiveOrbitLimitSet_of_tendsto Γ z (fun n => g * x n) (g • p)
  simpa only [Function.comp_def, mul_smul, hyperbolicCompactEmbedding_smul, hb, ← hgeo] using hlim

/-- Membership in the limit set is unchanged by any group element. -/
theorem projectiveOrbitLimitSet_smul_iff (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (g : Γ) (p : OnePoint ℝ) :
    g • p ∈ projectiveOrbitLimitSet Γ z ↔ p ∈ projectiveOrbitLimitSet Γ z := by
  constructor
  · intro hp
    simpa only [inv_smul_smul] using projectiveOrbitLimitSet_smul_mem Γ z g⁻¹ (g • p) hp
  · exact projectiveOrbitLimitSet_smul_mem Γ z g p

/-- Covariance of visual measures for the actual projective action. -/
theorem compactPoissonMeasure_projective_covariance (g : PSL(2, ℝ)) (z : ℍ) :
    Measure.map (fun p : OnePoint ℝ => g • p) (compactPoissonMeasure z) = compactPoissonMeasure (g • z) := by
  obtain ⟨a, rfl⟩ := slTwoProjective_surjective g
  exact compactPoissonMeasure_covariance a z

/-- The visual mass of the invariant limit set is constant along the orbit. -/
theorem projectiveOrbitLimitSet_visual_mass_orbit (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (g : Γ) :
    compactPoissonMeasure (g • z) (projectiveOrbitLimitSet Γ z) =
      compactPoissonMeasure z (projectiveOrbitLimitSet Γ z) := by
  change compactPoissonMeasure ((g : PSL(2, ℝ)) • z) _ = _
  rw [← compactPoissonMeasure_projective_covariance (g : PSL(2, ℝ)) z,
    Measure.map_apply (measurable_const_smul (g : PSL(2, ℝ))) (isClosed_projectiveOrbitLimitSet Γ z).measurableSet]
  congr 1
  ext p
  exact projectiveOrbitLimitSet_smul_iff Γ z g p

/-- A closed subset with full visual probability must be the entire boundary. -/
theorem closed_eq_univ_of_full_visual_mass (z : ℍ) (S : Set (OnePoint ℝ)) (hS : IsClosed S)
    (hfull : compactPoissonMeasure z S = 1) : S = Set.univ := by
  let := compactPoissonMeasure_probability z
  let := compactPoissonMeasure_isOpenPosMeasure z
  have hc : compactPoissonMeasure z Sᶜ = 0 := by
    rw [measure_compl hS.measurableSet (measure_ne_top _ _), measure_univ, hfull, tsub_self]
  have hem : Sᶜ = ∅ := by
    by_contra hne
    exact (hS.isOpen_compl.measure_ne_zero _ (Set.nonempty_iff_ne_empty.mpr hne)) hc
  simpa only [compl_compl, compl_empty] using congrArg (fun A : Set (OnePoint ℝ) => Aᶜ) hem

end Singularity
