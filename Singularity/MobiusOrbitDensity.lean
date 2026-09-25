import Singularity.DilationOrbit
import Singularity.DensityVector

/-!
# Identification of the lattice densities with actual matrix-orbit measures

The row at (n,j) is a logarithmic density for (a^n b_j)_*ν, where a is the
explicit diagonal dilation matrix. The identification is independent of
representatives and holds simultaneously for all rows on a common full-measure
set, supplying the actual ℓ² density columns used in the pairing argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

variable {J : Type*} [Fintype J] (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
  {τ : ℝ} (hτ : 0 < τ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
  (z : ℍ) (B : ℝ) (hB : 0 ≤ B)
  (hbound : ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z) (b : J → SL(2, ℝ))
  (q : ℤ → J → ℝ → ℝ) (hq : ∀ n j, Measurable (q n j)) (hpq : ∀ n j u, 0 ≤ q n j u)
  (hmeasure : ∀ n j, volume.withDensity (fun u => ENNReal.ofReal (q n j u)) =
    Measure.map (realBoundaryMobius (dilationMatrix τ ^ n * b j)) ν)

include hq hpq hmeasure

/-- Every row of the constructed lattice family is a density for the actual
matrix orbit measure, almost everywhere in logarithmic coordinates. -/
theorem mobiusOrbit_density_ae (n : ℤ) (j : J) :
    (mobiusBoundaryDensityFamily ε hε hτ ν z B hB hbound b).density (n, j) =ᵐ[volume]
      logBoundaryDensity ε (q n j) := by
  let μ := Measure.map (realBoundaryMobius (b j)) ν
  let f := poissonCappedDensity μ (b j • z).re (b j • z).im B
  have hm : volume.withDensity (fun u => ENNReal.ofReal (f u)) = μ :=
    poissonCappedDensity_measure μ
      (absolutelyContinuous_of_poisson_bound μ (b j • z) B (poisson_bound_map ν z B hbound (b j)))
      _ _ _ (rnDeriv_map_le_poisson ν z hB hbound (b j))
  have ho : volume.withDensity (fun u => ENNReal.ofReal (q n j u)) =
      Measure.map (fun u : ℝ => Real.exp ((n : ℝ) * τ) * u)
        (volume.withDensity (fun u => ENNReal.ofReal (f u))) := by
    rw [hm, hmeasure, dilationOrbit_map ν (absolutelyContinuous_of_poisson_bound ν z B hbound)]
  have ht := logBoundaryDensity_translation_of_map ε hε ((n : ℝ) * τ) f (q n j)
    (measurable_poissonCappedDensity _ _ _ _) (hq n j)
    (poissonCappedDensity_nonneg _ _ (b j • z).im_pos hB) (hpq n j) ho
  exact ht.symm

/-- Countability provides a single full-measure set on which every lattice
row has its prescribed orbit-density value. -/
theorem mobiusOrbit_density_all_ae :
    ∀ᵐ t : ℝ ∂volume, ∀ p : ℤ × J,
      (mobiusBoundaryDensityFamily ε hε hτ ν z B hB hbound b).density p t =
        logBoundaryDensity ε (q p.1 p.2) t := by
  exact ae_all_iff.mpr (fun p =>
    mobiusOrbit_density_ae ε hε hτ ν z B hB hbound b q hq hpq hmeasure p.1 p.2)

/-- The constructed ℓ² columns are the actual logarithmic orbit-density
vectors on that common full-measure set. -/
theorem mobiusOrbit_column_all_ae :
    ∀ᵐ t : ℝ ∂volume, ∀ p : ℤ × J,
      (mobiusBoundaryDensityFamily ε hε hτ ν z B hB hbound b).column t p =
        (logBoundaryDensity ε (q p.1 p.2) t : ℂ) := by
  filter_upwards [mobiusOrbit_density_all_ae ε hε hτ ν z B hB hbound b q hq hpq hmeasure] with t ht
  intro p
  rw [DensityFamily.column_apply, ht p]

/-- Analysis coordinates therefore pair against densities of (a^n b_j)_*ν. -/
theorem mobiusOrbit_analysis_apply (v : RealLineL2) (n : ℤ) (j : J) :
    (mobiusBoundaryDensityFamily ε hε hτ ν z B hB hbound b).analysis v (n, j) =
      ∫ t, (logBoundaryDensity ε (q n j) t : ℂ) * v t := by
  rw [DensityFamily.analysis_apply]
  apply integral_congr_ae
  filter_upwards [mobiusOrbit_density_ae ε hε hτ ν z B hB hbound b q hq hpq hmeasure n j] with t ht
  rw [ht]

end Singularity
