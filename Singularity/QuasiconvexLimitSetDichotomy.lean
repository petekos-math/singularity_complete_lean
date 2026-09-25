import Singularity.QuasiconvexConical
import Singularity.PoissonDensityPoint

/-!
# A quasiconvex orbit limit set is visual-null or the full boundary

If the limit set has positive visual measure, its finite real chart has
positive Lebesgue measure. Choose a Lebesgue density point, use vertical
Poisson concentration there, and track the vertical approach by the orbit.
Invariance makes the visual mass constant along the orbit. The comparison
then forces full mass, and closedness and full support force full boundary.
No discreteness or finite generation is required for this geometric statement.
-/

noncomputable section
open MeasureTheory Set Filter OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

/-- Exponentially decreasing positive heights converge to zero from above. -/
theorem exp_neg_nat_tendsto_nhdsGT_zero :
    Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop,
    Eventually.of_forall fun n => Real.exp_pos _⟩

/-- Compact visual mass along the vertical approach is exactly the real Poisson mass. -/
theorem compactPoisson_verticalApproach_apply (ξ t : ℝ) (S : Set (OnePoint ℝ)) (hS : MeasurableSet S) :
    compactPoissonMeasure (finiteVerticalApproach ξ t) S =
      halfPlanePoissonMeasure ξ (Real.exp (-t)) ((fun x : ℝ => (x : OnePoint ℝ)) ⁻¹' S) := by
  unfold compactPoissonMeasure compactRealMeasure
  rw [Measure.map_apply OnePoint.continuous_coe.measurable hS]
  rfl

/-- A quasiconvex orbit with positive visual limit-set mass has the full ideal boundary. -/
theorem quasiconvex_limitSet_eq_univ_of_visual_nonzero (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    (D : ℝ) (hqc : HyperbolicQuasiconvex (MulAction.orbit Γ z) D)
    (hpos : compactPoissonMeasure z (projectiveOrbitLimitSet Γ z) ≠ 0) :
    projectiveOrbitLimitSet Γ z = Set.univ := by
  let S : Set ℝ := (fun x : ℝ => (x : OnePoint ℝ)) ⁻¹' projectiveOrbitLimitSet Γ z
  have hS : MeasurableSet S := (isClosed_projectiveOrbitLimitSet Γ z).measurableSet.preimage
    OnePoint.continuous_coe.measurable
  have hvol : volume S ≠ 0 := by
    intro hz
    have hp : poissonBoundaryMeasure z S = 0 := (halfPlanePoissonMeasure_measureClass z.re z.im_pos).1 hz
    apply hpos
    unfold compactPoissonMeasure compactRealMeasure
    rw [Measure.map_apply OnePoint.continuous_coe.measurable (isClosed_projectiveOrbitLimitSet Γ z).measurableSet]
    exact hp
  have hrestr : volume.restrict S ≠ 0 := by
    intro hz
    apply hvol
    have hh := congrArg (fun ν : Measure ℝ => ν Set.univ) hz
    simpa using hh
  let : NeZero (volume.restrict S) := ⟨hrestr⟩
  obtain ⟨ξ, hξ, hlim⟩ := ((ae_restrict_mem hS).and (ae_halfPlanePoisson_compl_tendsto S hS)).exists
  apply full_limitSet_of_quasiconvex_poisson_concentration Γ z D hqc ξ hξ
  have ht := hlim.comp exp_neg_nat_tendsto_nhdsGT_zero
  have he (n : ℕ) : compactPoissonMeasure (finiteVerticalApproach ξ n) (projectiveOrbitLimitSet Γ z)ᶜ =
      halfPlanePoissonMeasure ξ (Real.exp (-(n : ℝ))) Sᶜ := by
    rw [compactPoisson_verticalApproach_apply _ _ _ (isClosed_projectiveOrbitLimitSet Γ z).measurableSet.compl]
    rfl
  simpa only [he, Function.comp_def] using ht

/-- The visual-null-or-full alternative for every quasiconvex projective orbit. -/
theorem quasiconvex_limitSet_visual_null_or_full (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    (D : ℝ) (hqc : HyperbolicQuasiconvex (MulAction.orbit Γ z) D) :
    compactPoissonMeasure z (projectiveOrbitLimitSet Γ z) = 0 ∨ projectiveOrbitLimitSet Γ z = Set.univ := by
  by_cases hz : compactPoissonMeasure z (projectiveOrbitLimitSet Γ z) = 0
  · exact Or.inl hz
  · exact Or.inr (quasiconvex_limitSet_eq_univ_of_visual_nonzero Γ z D hqc hz)

/-- A noncocompact quasiconvex orbit has visual-null limit set. -/
theorem noncocompact_quasiconvex_limitSet_visual_null (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    (D : ℝ) (hqc : HyperbolicQuasiconvex (MulAction.orbit Γ z) D)
    (hnc : ¬CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))) :
    compactPoissonMeasure z (projectiveOrbitLimitSet Γ z) = 0 := by
  rcases quasiconvex_limitSet_visual_null_or_full Γ z D hqc with hnull | hfull
  · exact hnull
  · exact (hnc (projective_cocompact_of_quasiconvex_full_limitSet Γ z D hqc hfull)).elim

end Singularity
