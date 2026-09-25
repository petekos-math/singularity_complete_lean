import Singularity.MobiusOrbitDensity

/-!
# Canonical densities for all matrix orbit measures

A single initial Poisson bound gives a measurable nonnegative density for each
actual Möbius pushforward. On a diagonal cyclic orbit these yield the density
columns and the nonzero orthogonal vector from the lattice obstruction.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal MatrixGroups UpperHalfPlane

namespace Singularity

/-- A canonical everywhere bounded density for a Möbius pushforward. -/
def mobiusPushforwardDensity (ν : Measure ℝ) (z : ℍ) (B : ℝ) (g : SL(2, ℝ)) : ℝ → ℝ :=
  poissonCappedDensity (Measure.map (realBoundaryMobius g) ν) (g • z).re (g • z).im B

theorem measurable_mobiusPushforwardDensity (ν : Measure ℝ) (z : ℍ) (B : ℝ) (g : SL(2, ℝ)) :
    Measurable (mobiusPushforwardDensity ν z B g) := measurable_poissonCappedDensity _ _ _ _

theorem mobiusPushforwardDensity_nonneg (ν : Measure ℝ) (z : ℍ) {B : ℝ}
    (hB : 0 ≤ B) (g : SL(2, ℝ)) (u : ℝ) : 0 ≤ mobiusPushforwardDensity ν z B g u :=
  poissonCappedDensity_nonneg _ _ (g • z).im_pos hB u

/-- The canonical representative gives the actual pushforward measure. -/
theorem mobiusPushforwardDensity_measure (ν : Measure ℝ) [IsFiniteMeasure ν]
    (z : ℍ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z) (g : SL(2, ℝ)) :
    volume.withDensity (fun u => ENNReal.ofReal (mobiusPushforwardDensity ν z B g u)) =
      Measure.map (realBoundaryMobius g) ν :=
  poissonCappedDensity_measure _
    (absolutelyContinuous_of_poisson_bound _ (g • z) B (poisson_bound_map ν z B hbound g))
    _ _ _ (rnDeriv_map_le_poisson ν z hB hbound g)

variable {J : Type*} [Fintype J] (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
  {τ : ℝ} (hτ : 0 < τ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
  (z : ℍ) (B : ℝ) (hB : 0 ≤ B)
  (hbound : ν ≤ ENNReal.ofReal B • poissonBoundaryMeasure z) (b : J → SL(2, ℝ))

/-- No independently chosen row densities are needed to identify all columns. -/
theorem mobiusOrbit_canonical_column_all_ae :
    ∀ᵐ t : ℝ ∂volume, ∀ p : ℤ × J,
      (mobiusBoundaryDensityFamily ε hε hτ ν z B hB hbound b).column t p =
        (logBoundaryDensity ε
          (mobiusPushforwardDensity ν z B (dilationMatrix τ ^ p.1 * b p.2)) t : ℂ) := by
  exact mobiusOrbit_column_all_ae ε hε hτ ν z B hB hbound b
    (fun n j => mobiusPushforwardDensity ν z B (dilationMatrix τ ^ n * b j))
    (fun n j => measurable_mobiusPushforwardDensity ν z B _)
    (fun n j => mobiusPushforwardDensity_nonneg ν z hB _)
    (fun n j => mobiusPushforwardDensity_measure ν z B hB hbound _)

include hε hτ hB hbound in
/-- The actual logarithmic orbit densities have a common nonzero L² annihilator. -/
theorem exists_nonzero_orthogonal_mobiusOrbit :
    ∃ v : RealLineL2, v ≠ 0 ∧ ∀ (n : ℤ) (j : J),
      (∫ t, (logBoundaryDensity ε
        (mobiusPushforwardDensity ν z B (dilationMatrix τ ^ n * b j)) t : ℂ) * v t) = 0 := by
  obtain ⟨v, hv, hk⟩ := mobiusBoundary_analysis_has_kernel ε hε hτ ν z B hB hbound b
  refine ⟨v, hv, fun n j => ?_⟩
  rw [← mobiusOrbit_analysis_apply ε hε hτ ν z B hB hbound b
    (fun n j => mobiusPushforwardDensity ν z B (dilationMatrix τ ^ n * b j))
    (fun n j => measurable_mobiusPushforwardDensity ν z B _)
    (fun n j => mobiusPushforwardDensity_nonneg ν z hB _)
    (fun n j => mobiusPushforwardDensity_measure ν z B hB hbound _) v n j, hk]
  rfl

end Singularity
