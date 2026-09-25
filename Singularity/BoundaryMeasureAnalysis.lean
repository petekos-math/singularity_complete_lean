import Singularity.BoundaryDensityAnalysis

/-!
# Boundary analysis from measures and a.e. Poisson bounds

A finite measure absolutely continuous with respect to real Lebesgue measure
has a real Radon–Nikodym density. Capping this density by the Poisson bound
chooses a measurable, everywhere nonnegative bounded representative while
preserving the measure. The boundary analysis family can therefore be built
from measures and a.e. bounds, without assuming preferred density functions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

/-- A canonical representative obeying the prescribed Poisson bound everywhere. -/
def poissonCappedDensity (ν : Measure ℝ) (x y B u : ℝ) : ℝ :=
  min ((ν.rnDeriv volume u).toReal) (B * halfPlanePoisson x y u)

theorem measurable_poissonCappedDensity (ν : Measure ℝ) (x y B : ℝ) :
    Measurable (poissonCappedDensity ν x y B) := by
  unfold poissonCappedDensity halfPlanePoisson
  fun_prop

theorem poissonCappedDensity_nonneg (ν : Measure ℝ) (x : ℝ) {y B : ℝ}
    (hy : 0 < y) (hB : 0 ≤ B) (u : ℝ) : 0 ≤ poissonCappedDensity ν x y B u :=
  le_min ENNReal.toReal_nonneg (mul_nonneg hB (halfPlanePoisson_nonneg x hy u))

theorem poissonCappedDensity_le (ν : Measure ℝ) (x y B u : ℝ) :
    poissonCappedDensity ν x y B u ≤ B * halfPlanePoisson x y u := min_le_right _ _

/-- Capping changes the Radon–Nikodym representative only on a null set. -/
theorem poissonCappedDensity_ae (ν : Measure ℝ) (x y B : ℝ)
    (hbound : ∀ᵐ u ∂volume, (ν.rnDeriv volume u).toReal ≤ B * halfPlanePoisson x y u) :
    poissonCappedDensity ν x y B =ᵐ[volume] fun u => (ν.rnDeriv volume u).toReal := by
  filter_upwards [hbound] with u hu
  exact min_eq_left hu

/-- The bounded representative is a density for the original measure itself. -/
theorem poissonCappedDensity_measure (ν : Measure ℝ) [SigmaFinite ν]
    (hac : ν ≪ volume) (x y B : ℝ)
    (hbound : ∀ᵐ u ∂volume, (ν.rnDeriv volume u).toReal ≤ B * halfPlanePoisson x y u) :
    volume.withDensity (fun u => ENNReal.ofReal (poissonCappedDensity ν x y B u)) = ν := by
  calc
    volume.withDensity (fun u => ENNReal.ofReal (poissonCappedDensity ν x y B u)) =
        volume.withDensity (ν.rnDeriv volume) := by
      apply withDensity_congr_ae
      filter_upwards [poissonCappedDensity_ae ν x y B hbound,
        Measure.rnDeriv_lt_top ν volume] with u hu hfin
      rw [hu, ENNReal.ofReal_toReal hfin.ne]
    _ = ν := Measure.withDensity_rnDeriv_eq ν volume hac

variable {J : Type*} [Fintype J] (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
  {τ : ℝ} (hτ : 0 < τ) (ν : J → Measure ℝ) [∀ j, SigmaFinite (ν j)]
  (hac : ∀ j, ν j ≪ volume) (hmass : ∀ j, ν j univ ≤ 1)
  (x y B : J → ℝ) (hy : ∀ j, 0 < y j) (hB : ∀ j, 0 ≤ B j)
  (hbound : ∀ j, ∀ᵐ u ∂volume,
    ((ν j).rnDeriv volume u).toReal ≤ B j * halfPlanePoisson (x j) (y j) u)

/-- Build the bounded lattice analysis directly from boundary measures with
a.e. Poisson bounds; all density representatives and mass bounds are supplied. -/
def boundaryMeasureDensityFamily : DensityFamily ℝ (ℤ × J) volume :=
  boundaryLogDensityFamily ε hε hτ (fun j => poissonCappedDensity (ν j) (x j) (y j) (B j))
    x y B (fun j => measurable_poissonCappedDensity _ _ _ _)
    (fun j => poissonCappedDensity_nonneg _ _ (hy j) (hB j))
    (fun j => by rw [poissonCappedDensity_measure _ (hac j) _ _ _ (hbound j)]; exact hmass j)
    hy hB (fun j => poissonCappedDensity_le _ _ _ _)

/-- These analysis operators have the nonzero kernel required by the Fourier
obstruction, now starting from measures instead of chosen density functions. -/
theorem boundaryMeasure_analysis_has_kernel :
    ∃ v : RealLineL2, v ≠ 0 ∧
      (boundaryMeasureDensityFamily ε hε hτ ν hac hmass x y B hy hB hbound).analysis v = 0 := by
  unfold boundaryMeasureDensityFamily
  exact boundaryLogDensity_analysis_has_kernel _ _ _ _ _ _ _ _ _ _ _ _ _

omit [Fintype J] in
include hac hbound in
/-- The chosen orbit density really represents dilation of the specified
boundary measure, not merely a formal translated profile. -/
theorem boundaryMeasure_orbit_density (n : ℤ) (j : J) :
    volume.withDensity (fun u => ENNReal.ofReal (dilatedBoundaryDensity ((n : ℝ) * τ)
      (poissonCappedDensity (ν j) (x j) (y j) (B j)) u)) =
      Measure.map (fun u : ℝ => Real.exp ((n : ℝ) * τ) * u) (ν j) := by
  rw [← dilatedBoundaryDensity_map _ _ (measurable_poissonCappedDensity _ _ _ _),
    poissonCappedDensity_measure _ (hac j) _ _ _ (hbound j)]

/-- Analysis coordinates can be computed using any nonnegative measurable
densities for the actual dilated boundary measures. -/
theorem boundaryMeasure_analysis_apply_of_map
    (g : ℤ → J → ℝ → ℝ) (hg : ∀ n j, Measurable (g n j)) (hpg : ∀ n j u, 0 ≤ g n j u)
    (hmap : ∀ n j, volume.withDensity (fun u => ENNReal.ofReal (g n j u)) =
      Measure.map (fun u : ℝ => Real.exp ((n : ℝ) * τ) * u) (ν j))
    (v : RealLineL2) (n : ℤ) (j : J) :
    (boundaryMeasureDensityFamily ε hε hτ ν hac hmass x y B hy hB hbound).analysis v (n, j) =
      ∫ t, (logBoundaryDensity ε (g n j) t : ℂ) * v t := by
  unfold boundaryMeasureDensityFamily
  apply boundaryLogDensity_analysis_apply_of_map
  · exact hg
  · exact hpg
  · intro n j
    rw [poissonCappedDensity_measure _ (hac j) _ _ _ (hbound j)]
    exact hmap n j

end Singularity
