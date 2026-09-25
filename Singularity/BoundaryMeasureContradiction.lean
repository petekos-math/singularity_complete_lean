import Singularity.BoundaryMeasureAnalysis
import Singularity.CurrentFactorization

/-!
# Analytic contradiction from boundary measures

This joins the measure-based construction of the positive analysis operator to
the current-to-Fourier argument. The unresolved geometric inputs remain visible:
absolute continuity and Poisson bounds for the actual hitting measures, the
current comparison, and the strip boundary-pairing representation.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Singularity

/-- Boundary subprobability measures with a.e. Poisson bounds cannot supply the
stated Liouville-current pairing through a finite lattice family. -/
theorem impossible_boundaryMeasure_current_identity {J : Type*} [Fintype J]
    {τ : ℝ} (hτ : 0 < τ) (ν : J → Measure ℝ) [∀ j, SigmaFinite (ν j)]
    (hac : ∀ j, ν j ≪ volume) (hmass : ∀ j, ν j univ ≤ 1)
    (x y B : J → ℝ) (hy : ∀ j, 0 < y j) (hB : ∀ j, 0 ≤ B j)
    (hbound : ∀ j, ∀ᵐ u ∂volume,
      ((ν j).rnDeriv volume u).toReal ≤ B j * halfPlanePoisson (x j) (y j) u)
    (Kminus : DensityFamily ℝ (ℤ × J) volume)
    (M : SequenceL2 (ℤ × J) →L[ℂ] SequenceL2 (ℤ × J))
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (hpF : ∀ z, 0 ≤ F z)
    (c : ℝ≥0∞) (hc : 0 < c) (hct : c < ⊤)
    (hcurrent : ((volume.restrict (Iio (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))).withDensity (fun z => ENNReal.ofReal (F z)) =
      c • ((volume.restrict (Iio (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))).withDensity
        (fun z => ENNReal.ofReal (realLiouvilleDensity z)))
    (hpair : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      densityPairingKernel Kminus
        (boundaryMeasureDensityFamily 1 (Or.inl rfl) hτ ν hac hmass x y B hy hB hbound)
        M z.1 z.2 = ((Real.exp z.1 * Real.exp z.2 * F (logBoundaryPair z) : ℝ) : ℂ)) :
    False := by
  have hfactor := liouville_factorization_of_current_identity Kminus
    (boundaryMeasureDensityFamily 1 (Or.inl rfl) hτ ν hac hmass x y B hy hB hbound)
    M F hF hpF c hcurrent hpair
  exact impossible_factorization (liouvilleConvolution c.toReal) _ M Kminus.analysis.adjoint
    hfactor (liouvilleConvolution_injective (ENNReal.toReal_pos hc.ne' hct.ne))
    (boundaryMeasure_analysis_has_kernel 1 (Or.inl rfl) hτ ν hac hmass x y B hy hB hbound)

end Singularity
