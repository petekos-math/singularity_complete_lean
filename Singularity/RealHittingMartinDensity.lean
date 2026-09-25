import Singularity.HittingMartinIdentification
import Singularity.FiniteBoundaryChart

/-!
# Actual Martin densities in the finite real boundary chart

Pulling a weighted compact-boundary measure to the real chart evaluates the
weight at finite boundary points. Consequently a real density q for the hitting
law gives q(u) K(x,u) as a density of every actual Möbius translate.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal
namespace Singularity

/-- Taking the finite chart commutes with a measurable weight when infinity has zero mass. -/
theorem finiteBoundaryMeasure_withDensity
    (ν : Measure (OnePoint ℝ)) (hinfty : ν {(∞ : OnePoint ℝ)} = 0)
    (f : OnePoint ℝ → ℝ≥0∞) (hf : Measurable f) :
    finiteBoundaryMeasure (ν.withDensity f) =
      (finiteBoundaryMeasure ν).withDensity (fun u : ℝ => f (u : OnePoint ℝ)) := by
  have h := map_withDensity_comp (fun u : ℝ => (u : OnePoint ℝ))
    OnePoint.continuous_coe.measurable (finiteBoundaryMeasure ν) f hf
  change compactRealMeasure ((finiteBoundaryMeasure ν).withDensity (fun u : ℝ => f (u : OnePoint ℝ))) =
    (compactRealMeasure (finiteBoundaryMeasure ν)).withDensity f at h
  rw [finiteBoundaryMeasure_reconstruct ν hinfty] at h
  rw [← h, finiteBoundaryMeasure_compactRealMeasure]

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) (z : ℍ)

local notation "ν" => geometricHittingMeasure Γ s μ hpos hmass hgen hgap z
local notation "K" => compactMartinPoint Γ s μ hpos hgen hgap horbit

/-- Every actual real-chart translate has Martin weight relative to the real hitting law. -/
theorem geometricHittingMeasure_real_martin_withDensity
    (hac : ν ≪ compactPoissonMeasure z) (x : Γ) :
    Measure.map (realBoundaryMobius (x : SL(2, ℝ))) (finiteBoundaryMeasure ν) =
      (finiteBoundaryMeasure ν).withDensity
        (fun u : ℝ => ENNReal.ofReal ((K (u : OnePoint ℝ)).val x)) := by
  rw [← finiteBoundaryMeasure_map ν z hac (x : SL(2, ℝ))]
  change finiteBoundaryMeasure (Measure.map (fun p : OnePoint ℝ => x • p) ν) = _
  rw [geometricHittingMeasure_martin_withDensity_basepoint Γ s μ hpos hmass hgen hgap horbit z x]
  exact finiteBoundaryMeasure_withDensity ν (compactPoisson_ac_infty ν z hac) _
    (continuous_compactMartinPoint_eval Γ s μ hpos hmass hgen hgap horbit x).measurable.ennreal_ofReal

/-- Multiplying a base Lebesgue density by the actual Martin kernel gives a
density for the actual translated hitting measure. -/
theorem geometricHittingMeasure_real_translate_density
    (hac : ν ≪ compactPoissonMeasure z) (q : ℝ → ℝ) (hq : Measurable q)
    (hpq : ∀ u, 0 ≤ q u)
    (hmeasure : volume.withDensity (fun u => ENNReal.ofReal (q u)) = finiteBoundaryMeasure ν)
    (x : Γ) :
    volume.withDensity (fun u : ℝ => ENNReal.ofReal (q u * (K (u : OnePoint ℝ)).val x)) =
      Measure.map (realBoundaryMobius (x : SL(2, ℝ))) (finiteBoundaryMeasure ν) := by
  have hK : Measurable (fun u : ℝ => ENNReal.ofReal ((K (u : OnePoint ℝ)).val x)) :=
    ((continuous_compactMartinPoint_eval Γ s μ hpos hmass hgen hgap horbit x).comp
      OnePoint.continuous_coe).measurable.ennreal_ofReal
  rw [geometricHittingMeasure_real_martin_withDensity Γ s μ hpos hmass hgen hgap horbit z hac x,
    ← hmeasure, ← withDensity_mul _ hq.ennreal_ofReal hK]
  congr 1
  funext u
  exact ENNReal.ofReal_mul (hpq u)

include horbit in
/-- The same density formula uses the earlier finite-endpoint Martin coordinates. -/
theorem geometricHittingMeasure_real_translate_ray_density
    (hac : ν ≪ compactPoissonMeasure z) (q : ℝ → ℝ) (hq : Measurable q)
    (hpq : ∀ u, 0 ≤ q u)
    (hmeasure : volume.withDensity (fun u => ENNReal.ofReal (q u)) = finiteBoundaryMeasure ν)
    (x : Γ) :
    volume.withDensity (fun u : ℝ => ENNReal.ofReal (q u * (rayMartinPoint Γ s μ hpos hgen hgap u).val x)) =
      Measure.map (realBoundaryMobius (x : SL(2, ℝ))) (finiteBoundaryMeasure ν) := by
  simpa only [compactMartinPoint_coe Γ s μ hpos hmass hgen hgap horbit] using
    geometricHittingMeasure_real_translate_density Γ s μ hpos hmass hgen hgap horbit z hac q hq hpq hmeasure x

end Singularity
