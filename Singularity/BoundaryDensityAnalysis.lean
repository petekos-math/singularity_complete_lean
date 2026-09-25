import Singularity.LogBoundaryDensity

/-!
# Lattice analysis from boundary subprobability densities

The input consists of finitely many real boundary densities, their total-mass
bounds, and Poisson domination. Logarithmic change of variables supplies all
integrability, row-mass, and decay hypotheses of the existing analysis operator.
Dilation pushforwards identify its coordinates with any chosen density
representatives for the boundary orbit measures.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

variable {J : Type*} [Fintype J] (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
  {τ : ℝ} (hτ : 0 < τ) (f : J → ℝ → ℝ) (x y B : J → ℝ)
  (hf : ∀ j, Measurable (f j)) (hpf : ∀ j u, 0 ≤ f j u)
  (hmass : ∀ j, (volume.withDensity (fun u => ENNReal.ofReal (f j u))) univ ≤ 1)
  (hy : ∀ j, 0 < y j) (hB : ∀ j, 0 ≤ B j)
  (hdom : ∀ j u, f j u ≤ B j * halfPlanePoisson (x j) (y j) u)

/-- Construct the bounded density analysis family directly from real-boundary
densities. No logarithmic integrability or mass hypotheses are added. -/
def boundaryLogDensityFamily : DensityFamily ℝ (ℤ × J) volume :=
  poissonDominatedDensityFamily hτ (fun j => logBoundaryDensity ε (f j))
    (fun j => ε * x j) y B hy hB
    (fun j => (measurable_logBoundaryDensity ε (f j) (hf j)).aestronglyMeasurable)
    (fun j => logBoundaryDensity_nonneg ε (f j) (hpf j))
    (fun j => (logBoundaryDensity_integrable_mass ε hε (f j) (hf j) (hpf j) (hmass j)).2)
    (fun j => logBoundaryDensity_poisson_domination ε hε (f j) (x j) (y j) (B j) (hdom j))

/-- Its coordinates pair against the densities of actual dilation pushforwards
in logarithmic coordinates. -/
theorem boundaryLogDensity_analysis_apply (v : RealLineL2) (n : ℤ) (j : J) :
    (boundaryLogDensityFamily ε hε hτ f x y B hf hpf hmass hy hB hdom).analysis v (n, j) =
      ∫ t, (logBoundaryDensity ε (dilatedBoundaryDensity ((n : ℝ) * τ) (f j)) t : ℂ) * v t := by
  unfold boundaryLogDensityFamily
  rw [poissonDominated_analysis_apply]
  simp only [logBoundaryDensity_dilation]

/-- The finite-family lattice obstruction applies to these constructed
boundary-density analysis operators. -/
theorem boundaryLogDensity_analysis_has_kernel :
    ∃ v : RealLineL2, v ≠ 0 ∧
      (boundaryLogDensityFamily ε hε hτ f x y B hf hpf hmass hy hB hdom).analysis v = 0 := by
  unfold boundaryLogDensityFamily
  exact poissonDominated_analysis_has_kernel _ _ _ _ _ _ _ _ _ _ _

/-- Any measurable nonnegative representatives of the same orbit measures give
the same analysis coordinates. Only equality of pushforward measures is used. -/
theorem boundaryLogDensity_analysis_apply_of_map
    (g : ℤ → J → ℝ → ℝ) (hg : ∀ n j, Measurable (g n j))
    (hpg : ∀ n j u, 0 ≤ g n j u)
    (hmap : ∀ n j, volume.withDensity (fun u => ENNReal.ofReal (g n j u)) =
      Measure.map (fun u : ℝ => Real.exp ((n : ℝ) * τ) * u)
        (volume.withDensity (fun u => ENNReal.ofReal (f j u))))
    (v : RealLineL2) (n : ℤ) (j : J) :
    (boundaryLogDensityFamily ε hε hτ f x y B hf hpf hmass hy hB hdom).analysis v (n, j) =
      ∫ t, (logBoundaryDensity ε (g n j) t : ℂ) * v t := by
  rw [boundaryLogDensity_analysis_apply]
  apply integral_congr_ae
  have h := logBoundaryDensity_translation_of_map ε hε ((n : ℝ) * τ)
    (f j) (g n j) (hf j) (hg n j) (hpf j) (hpg n j) (hmap n j)
  filter_upwards [h] with t ht
  rw [logBoundaryDensity_dilation, ht]

end Singularity
