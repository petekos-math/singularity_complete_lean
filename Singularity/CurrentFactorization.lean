import Singularity.LogBoundaryMeasure
import Singularity.KernelFactorization

/-!
# From a scalar current comparison to the Fourier contradiction

The current identity on opposite real half-lines is transported to logarithmic
coordinates with the proved Jacobian. A boundary pairing representation then
implies the operator factorization already ruled out by Fourier analysis.
The geometric current identity and boundary pairing remain explicit inputs.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Singularity

/-- The bounded-operator factorization follows from a measure-level current
identity and the logarithmic boundary pairing. -/
theorem liouville_factorization_of_current_identity {ι : Type*} [Countable ι]
    (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (hpF : ∀ z, 0 ≤ F z) (c : ℝ≥0∞)
    (hcurrent : ((volume.restrict (Iio (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))).withDensity (fun z => ENNReal.ofReal (F z)) =
      c • ((volume.restrict (Iio (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))).withDensity
        (fun z => ENNReal.ofReal (realLiouvilleDensity z)))
    (hpair : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      densityPairingKernel Kminus Kplus M z.1 z.2 =
        ((Real.exp z.1 * Real.exp z.2 * F (logBoundaryPair z) : ℝ) : ℂ)) :
    liouvilleConvolution c.toReal = densityFactorization Kminus Kplus M := by
  apply liouville_factorization_of_kernel_identity_prod
  filter_upwards [hpair, log_current_density_identity F hF hpF c hcurrent] with z hz hden
  rw [hz, hden]

/-- The full analytic contradiction now accepts a current identity instead of
an assumed cosh-kernel identity. Its geometric inputs are still explicit. -/
theorem impossible_liouville_current_identity {J : Type*} [Fintype J]
    {τ : ℝ} (hτ : 0 < τ) (c : ℝ≥0∞) (hc : 0 < c) (hct : c < ⊤)
    (k : J → ℝ → ℝ) (C : J → ℝ) (hC : ∀ j, 0 ≤ C j) (hk : ∀ j t, 0 ≤ k j t)
    (hint : ∀ j, Integrable (k j)) (hmass : ∀ j, ∫ t, k j t ≤ 1)
    (hdecay : ∀ j t, k j t ≤ C j * Real.exp (-|t|))
    (Kminus : DensityFamily ℝ (ℤ × J) volume)
    (M : SequenceL2 (ℤ × J) →L[ℂ] SequenceL2 (ℤ × J))
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) (hpF : ∀ z, 0 ≤ F z)
    (hcurrent : ((volume.restrict (Iio (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))).withDensity (fun z => ENNReal.ofReal (F z)) =
      c • ((volume.restrict (Iio (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))).withDensity
        (fun z => ENNReal.ofReal (realLiouvilleDensity z)))
    (hpair : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      densityPairingKernel Kminus
        (translatedDensityFamily hτ k C hC hk hint hmass hdecay) M z.1 z.2 =
        ((Real.exp z.1 * Real.exp z.2 * F (logBoundaryPair z) : ℝ) : ℂ)) : False := by
  exact impossible_liouville_factorization hτ (ENNReal.toReal_pos hc.ne' hct.ne)
    k C hC hk hint hmass hdecay M Kminus.analysis.adjoint
    (liouville_factorization_of_current_identity Kminus
      (translatedDensityFamily hτ k C hC hk hint hmass hdecay) M F hF hpF c hcurrent hpair)

end Singularity
