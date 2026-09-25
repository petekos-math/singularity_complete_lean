import Singularity.PoissonDomination

/-!
# Boundary analysis from a single bounded measure and Möbius translates

A bound by B times one Poisson measure supplies all bounds for the finitely
many translated base measures. Thus the bounded analysis family needs no
independent Poisson-bound hypotheses at the orbit representatives.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

variable {J : Type*} [Fintype J] (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
  {τ : ℝ} (hτ : 0 < τ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
  (z : ℍ) (B : ℝ) (hB : 0 ≤ B)
  (hbound : ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z) (g : J → SL(2, ℝ))

/-- The actual analysis family for finitely many Möbius translates of one
bounded boundary probability measure. -/
def mobiusBoundaryDensityFamily : DensityFamily ℝ (ℤ × J) volume :=
  boundaryMeasureDensityFamily ε hε hτ (fun j => Measure.map (realBoundaryMobius (g j)) ν)
    (fun j => absolutelyContinuous_of_poisson_bound _ (g j • z) B
      (poisson_bound_map ν z B hbound (g j)))
    (fun j => by simp)
    (fun j => (g j • z).re) (fun j => (g j • z).im) (fun _ => B)
    (fun j => (g j • z).im_pos) (fun _ => hB)
    (fun j => rnDeriv_map_le_poisson ν z hB hbound (g j))

/-- The constructed analysis operator has a nonzero kernel, with every
Poisson bound obtained by actual Möbius covariance. -/
theorem mobiusBoundary_analysis_has_kernel :
    ∃ v : RealLineL2, v ≠ 0 ∧
      (mobiusBoundaryDensityFamily ε hε hτ ν z B hB hbound g).analysis v = 0 := by
  unfold mobiusBoundaryDensityFamily
  exact boundaryMeasure_analysis_has_kernel _ _ _ _ _ _ _ _ _ _ _ _

end Singularity
