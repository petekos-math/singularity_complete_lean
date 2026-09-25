import Singularity.HittingMartinDensity
import Singularity.CompactMartinMinimality

/-!
# Simultaneous identification and minimality of actual hitting derivatives

Base-point independence and countability identify all derivative coordinates on
one full-measure set. The resulting harmonic functions are actual Martin boundary
points and are minimal in the positive harmonic cone.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

/-- The exact Martin density formula holds for every geometric base point. -/
theorem geometricHittingMeasure_martin_withDensity_basepoint (z : ℍ) (x : Γ) :
    Measure.map (fun p : OnePoint ℝ => x • p)
      (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) =
    (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z).withDensity
      (fun p => ENNReal.ofReal ((compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x)) := by
  rw [geometricHittingMeasure_basepoint Γ s μ hpos hmass hgen hgap z UpperHalfPlane.I]
  exact geometricHittingMeasure_martin_withDensity Γ s μ hpos hmass hgen hgap horbit x

/-- All real derivative coordinates are identified on one common full-measure set. -/
theorem geometricHittingMeasure_realDensity_eq_martin_all (z : ℍ) :
    let ν := geometricHittingMeasure Γ s μ hpos hmass hgen hgap z
    ∀ᵐ p ∂ν, ∀ x : Γ, stationaryRealDensity ν x p =
      (compactMartinPoint Γ s μ hpos hgen hgap horbit p).val x := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  dsimp only
  rw [geometricHittingMeasure_basepoint Γ s μ hpos hmass hgen hgap z UpperHalfPlane.I]
  exact ae_all_iff.mpr (geometricHittingMeasure_realDensity_eq_martin Γ s μ hpos hmass hgen hgap horbit)

include horbit in
/-- The actual derivative, as a function of the starting state, is a Martin boundary point. -/
theorem geometricHittingMeasure_density_mem_martinBoundary (z : ℍ) :
    let ν := geometricHittingMeasure Γ s μ hpos hmass hgen hgap z
    ∀ᵐ p ∂ν, (fun x : Γ => stationaryRealDensity ν x p) ∈ martinBoundary s μ 1 := by
  filter_upwards [geometricHittingMeasure_realDensity_eq_martin_all Γ s μ hpos hmass hgen hgap horbit z]
    with p hp
  have he := funext hp
  rw [he]
  exact (compactMartinPoint Γ s μ hpos hgen hgap horbit p).property

include horbit in
/-- Almost every actual hitting derivative is minimal in the positive harmonic cone. -/
theorem geometricHittingMeasure_density_minimal (z : ℍ) :
    let ν := geometricHittingMeasure Γ s μ hpos hmass hgen hgap z
    ∀ᵐ p ∂ν, ∀ f : Γ → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ stationaryRealDensity ν x p) →
      (∀ x, ∑ a ∈ s, μ a * f (x * a) = f x) →
      ∃ c ∈ Icc (0 : ℝ) 1, ∀ x, f x = c * stationaryRealDensity ν x p := by
  filter_upwards [geometricHittingMeasure_realDensity_eq_martin_all Γ s μ hpos hmass hgen hgap horbit z]
    with p hp
  intro f hf hfh
  simp only [hp] at hf ⊢
  exact compactMartinPoint_minimal Γ s μ hpos hmass hgen hgap horbit p f hf hfh

end Singularity
