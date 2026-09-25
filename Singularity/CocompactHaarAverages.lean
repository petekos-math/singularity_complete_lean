import Singularity.CocompactHaarMeasure
import Singularity.ErgodicCesaro

/-!
# Subsequence ergodic averages on the actual compact Haar quotient

Normalize the previously constructed finite nonzero Haar quotient measure.
The actual positive diagonal time is ergodic for this probability, so every
bounded measurable observable has almost-everywhere subsequential averages
converging to its space average.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped MatrixGroups UpperHalfPlane Topology

namespace Singularity

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
  (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν]

/-- The normalized actual Haar quotient measure. -/
def cocompactHaarQuotientProbability : Measure (SL(2, ℝ) ⧸ Γ) :=
  (cocompactHaarQuotientMeasure Γ ν univ)⁻¹ • cocompactHaarQuotientMeasure Γ ν

theorem cocompactHaarQuotientProbability_probability :
    IsProbabilityMeasure (cocompactHaarQuotientProbability Γ ν) := by
  let := cocompactHaarQuotientMeasure_finite Γ ν
  let : NeZero (cocompactHaarQuotientMeasure Γ ν) :=
    ⟨cocompactHaarQuotientMeasure_ne_zero Γ ν⟩
  unfold cocompactHaarQuotientProbability
  infer_instance

/-- Normalizing the Haar quotient does not change its null sets. -/
theorem cocompactHaarQuotientProbability_measureClass :
    cocompactHaarQuotientProbability Γ ν ≪ cocompactHaarQuotientMeasure Γ ν ∧
      cocompactHaarQuotientMeasure Γ ν ≪ cocompactHaarQuotientProbability Γ ν := by
  let := cocompactHaarQuotientMeasure_finite Γ ν
  exact ⟨smul_absolutelyContinuous,
    absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))⟩

/-- Positive diagonal time maps are ergodic for the actual normalized quotient. -/
theorem cocompactHaarQuotientProbability_dilation_ergodic (τ : ℝ) (hτ : 0 < τ) :
    Ergodic (fun x : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • x)
      (cocompactHaarQuotientProbability Γ ν) :=
  (cocompactHaarQuotientMeasure_dilation_ergodic Γ ν τ hτ).smul_measure _

/-- Actual quotient orbit averages converge along a subsequence to their Haar average. -/
theorem cocompactHaar_birkhoffAverage_subsequence (τ : ℝ) (hτ : 0 < τ)
    (f : SL(2, ℝ) ⧸ Γ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂cocompactHaarQuotientProbability Γ ν,
      Tendsto (fun k => birkhoffAverage ℝ (fun y : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • y)
        f (ns k) x) atTop (𝓝 (∫ y, f y ∂cocompactHaarQuotientProbability Γ ν)) := by
  let := cocompactHaarQuotientProbability_probability Γ ν
  exact ergodic_bounded_birkhoffAverage_subsequence _ _
    (cocompactHaarQuotientProbability_dilation_ergodic Γ ν τ hτ) f hf C hC hbound

end Singularity
