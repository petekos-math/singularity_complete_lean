import Singularity.CocompactGroupQuotient
import Singularity.QuotientDilationErgodicity

/-!
# The actual finite ergodic Haar quotient measure

Starting from discreteness and compactness of Γ\ℍ, choose the constructed
measurable fundamental domain and push forward restricted Haar measure.
Its finiteness, nonzero mass, invariance and diagonal ergodicity are proved;
none of them is supplied as a quotient-measure assumption.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

attribute [local instance] slTwo_locallyCompactSpace slTwo_polishSpace

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
  (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν]

/-- A measurable finite fundamental domain supplied by cocompactness. -/
def cocompactHaarDomain : Set SL(2, ℝ) :=
  (exists_cocompact_finite_fundamentalDomain Γ ν).choose

theorem cocompactHaarDomain_measurable : MeasurableSet (cocompactHaarDomain Γ ν) :=
  (exists_cocompact_finite_fundamentalDomain Γ ν).choose_spec.1

theorem cocompactHaarDomain_fundamental : IsFundamentalDomain Γ.op (cocompactHaarDomain Γ ν) ν :=
  (exists_cocompact_finite_fundamentalDomain Γ ν).choose_spec.2.1

theorem cocompactHaarDomain_finite : ν (cocompactHaarDomain Γ ν) < ⊤ :=
  (exists_cocompact_finite_fundamentalDomain Γ ν).choose_spec.2.2

/-- The resulting quotient measure on right cosets. -/
def cocompactHaarQuotientMeasure : Measure (SL(2, ℝ) ⧸ Γ) :=
  (ν.restrict (cocompactHaarDomain Γ ν)).map QuotientGroup.mk

theorem cocompactHaarQuotientMeasure_finite :
    IsFiniteMeasure (cocompactHaarQuotientMeasure Γ ν) := by
  let : Fact (ν (cocompactHaarDomain Γ ν) < ⊤) := ⟨cocompactHaarDomain_finite Γ ν⟩
  unfold cocompactHaarQuotientMeasure
  infer_instance

theorem cocompactHaarQuotientMeasure_univ :
    cocompactHaarQuotientMeasure Γ ν univ = ν (cocompactHaarDomain Γ ν) := by
  have hm : Measurable (QuotientGroup.mk : SL(2, ℝ) → SL(2, ℝ) ⧸ Γ) :=
    measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  rw [cocompactHaarQuotientMeasure, Measure.map_apply hm MeasurableSet.univ]
  simp

/-- The constructed quotient has positive mass. -/
theorem cocompactHaarQuotientMeasure_ne_zero : cocompactHaarQuotientMeasure Γ ν ≠ 0 := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := slTwo_haar_rightInvariant ν
  let : Countable Γ := countable_of_Lindelof_of_discrete
  have hp := (cocompactHaarDomain_fundamental Γ ν).measure_ne_zero (NeZero.ne ν)
  intro hzero
  apply hp
  rw [← cocompactHaarQuotientMeasure_univ Γ ν, hzero]
  rfl

/-- The fundamental-domain formula holds for the constructed quotient measure. -/
theorem cocompactHaarQuotientMeasure_formula :
    QuotientMeasureEqMeasurePreimage ν (cocompactHaarQuotientMeasure Γ ν) := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := slTwo_haar_rightInvariant ν
  let : Countable Γ := countable_of_Lindelof_of_discrete
  exact (cocompactHaarDomain_fundamental Γ ν).quotientMeasureEqMeasurePreimage_quotientMeasure

/-- The constructed quotient measure is invariant under the full special-linear group. -/
theorem cocompactHaarQuotientMeasure_invariant :
    SMulInvariantMeasure SL(2, ℝ) (SL(2, ℝ) ⧸ Γ) (cocompactHaarQuotientMeasure Γ ν) := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := cocompactHaarQuotientMeasure_formula Γ ν
  let := (cocompactHaarDomain_fundamental Γ ν).hasFundamentalDomain ν
  exact QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient ν

/-- Positive diagonal times are ergodic for the actual quotient measure. -/
theorem cocompactHaarQuotientMeasure_dilation_ergodic (τ : ℝ) (hτ : 0 < τ) :
    Ergodic (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • x)
      (cocompactHaarQuotientMeasure Γ ν) :=
  ergodic_dilation_fundamentalDomain Γ ν (cocompactHaarDomain_fundamental Γ ν)
    (cocompactHaarDomain_finite Γ ν) τ hτ

end Singularity
