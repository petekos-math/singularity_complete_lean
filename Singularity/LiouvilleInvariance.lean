import Singularity.LiouvilleMobius

/-!
# Invariance of the concrete compact Liouville current

The finite-chart invariance transfers to all distinct compact endpoints.
The exceptional poles of the chart have zero current measure, proved through
its absolute continuity with respect to planar product Lebesgue measure.
No ergodicity statement is assumed or concluded here.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups

namespace Singularity

/-- The compact diagonal action preserves the explicitly constructed Liouville current. -/
theorem compactLiouvilleCurrent_invariant (g : SL(2, ℝ)) :
    Measure.map (fun p : BoundaryPair => g • p) compactLiouvilleCurrent = compactLiouvilleCurrent := by
  let D : OnePoint ℝ × OnePoint ℝ → OnePoint ℝ × OnePoint ℝ := fun p => (g • p.1, g • p.2)
  let R : ℝ × ℝ → ℝ × ℝ := Prod.map (realBoundaryMobius g) (realBoundaryMobius g)
  have hD : Measurable D := by dsimp [D]; fun_prop
  have hR : Measurable R := (measurable_realBoundaryMobius g).prodMap (measurable_realBoundaryMobius g)
  have hc : D ∘ realBoundaryPairChart =ᵐ[realLiouvilleMeasure] realBoundaryPairChart ∘ R := by
    apply realLiouvilleMeasure_absolutelyContinuous.ae_eq
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (realBoundaryMobius_denominator_ae g),
      Measure.quasiMeasurePreserving_snd.ae (realBoundaryMobius_denominator_ae g)] with p hx hy
    exact Prod.ext (compactBoundary_smul_finite g p.1 hx) (compactBoundary_smul_finite g p.2 hy)
  apply measurableEmbedding_boundaryPair.map_injective
  calc
    Measure.map Subtype.val (Measure.map (fun p : BoundaryPair => g • p) compactLiouvilleCurrent) =
        Measure.map D (Measure.map Subtype.val compactLiouvilleCurrent) := by
      rw [Measure.map_map measurable_subtype_coe (measurable_const_smul g),
        Measure.map_map hD measurable_subtype_coe]
      rfl
    _ = Measure.map D (Measure.map realBoundaryPairChart realLiouvilleMeasure) := by
      rw [compactLiouvilleCurrent_chart]
    _ = Measure.map (D ∘ realBoundaryPairChart) realLiouvilleMeasure :=
      Measure.map_map hD measurable_realBoundaryPairChart
    _ = Measure.map (realBoundaryPairChart ∘ R) realLiouvilleMeasure := Measure.map_congr hc
    _ = Measure.map realBoundaryPairChart (Measure.map R realLiouvilleMeasure) :=
      (Measure.map_map measurable_realBoundaryPairChart hR).symm
    _ = Measure.map realBoundaryPairChart realLiouvilleMeasure := by rw [realLiouvilleMeasure_mobius]
    _ = Measure.map Subtype.val compactLiouvilleCurrent := compactLiouvilleCurrent_chart.symm

/-- Liouville invariance as the standard invariant-measure property. -/
theorem compactLiouvilleCurrent_smulInvariant :
    SMulInvariantMeasure SL(2, ℝ) BoundaryPair compactLiouvilleCurrent := by
  constructor
  intro g A hA
  rw [← Measure.map_apply (measurable_const_smul g) hA, compactLiouvilleCurrent_invariant]

/-- Every Fuchsian subgroup preserves this same reference current. -/
theorem compactLiouvilleCurrent_subgroupInvariant (Γ : Subgroup SL(2, ℝ)) :
    SMulInvariantMeasure Γ BoundaryPair compactLiouvilleCurrent := by
  constructor
  intro g A hA
  change compactLiouvilleCurrent ((fun p : BoundaryPair => (g : SL(2, ℝ)) • p) ⁻¹' A) = _
  rw [← Measure.map_apply (measurable_const_smul (g : SL(2, ℝ))) hA, compactLiouvilleCurrent_invariant]

end Singularity
