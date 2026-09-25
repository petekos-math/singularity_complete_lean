import Singularity.MautnerErgodicity
import Singularity.QuotientErgodicity
import Singularity.SLTwoHaar
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

/-!
# Ergodicity of diagonal time maps on finite Haar quotients

This combines Haar unimodularity, full-group quotient ergodicity, and the
Mautner argument. It still requires a Haar fundamental domain and a finite
regular quotient measure; the identification with the Liouville boundary-pair
current is a separate geometric step.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups

namespace Singularity

/-- Every positive diagonal time is ergodic on a finite regular Haar quotient. -/
theorem ergodic_dilation_quotient
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (Γ : Subgroup SL(2, ℝ)) [Countable Γ] [T2Space (SL(2, ℝ) ⧸ Γ)]
    (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν]
    (μ : Measure (SL(2, ℝ) ⧸ Γ)) [IsFiniteMeasure μ]
    [QuotientMeasureEqMeasurePreimage ν μ] {F : Set SL(2, ℝ)}
    (hF : IsFundamentalDomain Γ.op F ν) (τ : ℝ) (hτ : 0 < τ) :
    Ergodic (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • x) μ := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := slTwo_haar_rightInvariant ν
  let : HasFundamentalDomain Γ.op SL(2, ℝ) ν := ⟨⟨F, hF⟩⟩
  let : SMulInvariantMeasure SL(2, ℝ) (SL(2, ℝ) ⧸ Γ) μ :=
    QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient ν
  let := ergodicSMul_quotient_of_fundamentalDomain Γ ν μ hF
  exact ergodic_dilation_of_ergodic_slTwo μ τ hτ

/-- For a discrete subgroup, the separation and countability conditions are automatic. -/
theorem ergodic_dilation_discrete_quotient
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν]
    (μ : Measure (SL(2, ℝ) ⧸ Γ)) [IsFiniteMeasure μ]
    [QuotientMeasureEqMeasurePreimage ν μ] {F : Set SL(2, ℝ)}
    (hF : IsFundamentalDomain Γ.op F ν) (τ : ℝ) (hτ : 0 < τ) :
    Ergodic (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • x) μ := by
  let := slTwo_polishSpace
  let : Countable Γ := countable_of_Lindelof_of_discrete
  exact ergodic_dilation_quotient Γ ν μ hF τ hτ

/-- Constructing the quotient measure from a finite Haar fundamental domain supplies
all measure and ergodicity hypotheses of the diagonal-time conclusion. -/
theorem ergodic_dilation_fundamentalDomain
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν] {F : Set SL(2, ℝ)}
    (hF : IsFundamentalDomain Γ.op F ν) (hfinite : ν F < ⊤)
    (τ : ℝ) (hτ : 0 < τ) :
    Ergodic (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • x)
      ((ν.restrict F).map (QuotientGroup.mk : SL(2, ℝ) → SL(2, ℝ) ⧸ Γ)) := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := slTwo_haar_rightInvariant ν
  let : Countable Γ := countable_of_Lindelof_of_discrete
  let : Fact (ν F < ⊤) := ⟨hfinite⟩
  let := hF.quotientMeasureEqMeasurePreimage_quotientMeasure
  exact ergodic_dilation_discrete_quotient Γ ν _ hF τ hτ

end Singularity
