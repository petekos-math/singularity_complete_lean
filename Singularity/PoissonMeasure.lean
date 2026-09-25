import Singularity.LogBoundaryDensity
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Probability measures from the upper-half-plane Poisson kernel

The explicit Poisson density defines a probability measure, equivalent to
Lebesgue measure. Translation and positive dilation of the real boundary
transport it to the measure at the correspondingly transformed interior point.
-/

noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace Singularity

/-- The measure on the finite real boundary chart with Poisson density. -/
def halfPlanePoissonMeasure (x y : ℝ) : Measure ℝ :=
  volume.withDensity (fun u => ENNReal.ofReal (halfPlanePoisson x y u))

theorem measurable_halfPlanePoisson (x y : ℝ) : Measurable (halfPlanePoisson x y) := by
  unfold halfPlanePoisson
  fun_prop

theorem halfPlanePoisson_pos (x : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    0 < halfPlanePoisson x y u := by
  unfold halfPlanePoisson
  positivity

/-- The explicit Poisson kernel agrees with the normalized Cauchy density. -/
theorem halfPlanePoisson_eq_cauchyPDFReal (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    halfPlanePoisson x y = cauchyPDFReal x ⟨y, hy⟩ := by
  funext u
  change y / (Real.pi * ((u - x) ^ 2 + y ^ 2)) =
    Real.pi⁻¹ * y * ((u - x) ^ 2 + y ^ 2)⁻¹
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem integrable_halfPlanePoisson (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (halfPlanePoisson x y) := by
  rw [halfPlanePoisson_eq_cauchyPDFReal x hy.le]
  exact integrable_cauchyPDFReal x

theorem integral_halfPlanePoisson (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ u, halfPlanePoisson x y u = 1 := by
  rw [halfPlanePoisson_eq_cauchyPDFReal x hy.le]
  exact integral_cauchyPDFReal_eq_one x (by
    intro h
    exact hy.ne' (congrArg (fun a : ℝ≥0 => (a : ℝ)) h))

/-- The Poisson measure has total mass one. -/
theorem halfPlanePoissonMeasure_probability (x : ℝ) {y : ℝ} (hy : 0 < y) :
    IsProbabilityMeasure (halfPlanePoissonMeasure x y) := by
  constructor
  rw [halfPlanePoissonMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_halfPlanePoisson x hy)
      (Filter.Eventually.of_forall (halfPlanePoisson_nonneg x hy)),
    integral_halfPlanePoisson x hy, ENNReal.ofReal_one]

/-- Positivity of the kernel gives equivalence with real Lebesgue measure. -/
theorem halfPlanePoissonMeasure_measureClass (x : ℝ) {y : ℝ} (hy : 0 < y) :
    halfPlanePoissonMeasure x y ≪ volume ∧ volume ≪ halfPlanePoissonMeasure x y :=
  positive_real_weight_measureClass volume (halfPlanePoisson x y)
    (measurable_halfPlanePoisson x y) (Filter.Eventually.of_forall (halfPlanePoisson_pos x hy))

/-- Translation covariance of the Poisson density. -/
theorem halfPlanePoisson_translate (x y a u : ℝ) :
    halfPlanePoisson x y (u - a) = halfPlanePoisson (a + x) y u := by
  unfold halfPlanePoisson
  congr 3
  ring

/-- Translation of the real boundary transports its Poisson measure. -/
theorem halfPlanePoissonMeasure_translate (x y a : ℝ) :
    Measure.map (fun u : ℝ => a + u) (halfPlanePoissonMeasure x y) =
      halfPlanePoissonMeasure (a + x) y := by
  have h := map_withDensity_equiv (MeasurableEquiv.addLeft a) volume
    (fun u => ENNReal.ofReal (halfPlanePoisson x y u))
    (measurable_halfPlanePoisson x y).ennreal_ofReal
  change Measure.map (fun u => a + u) (halfPlanePoissonMeasure x y) =
    (Measure.map (fun u => a + u) volume).withDensity
      (fun u => ENNReal.ofReal (halfPlanePoisson x y (-a + u))) at h
  rw [(measurePreserving_add_left volume a).map_eq] at h
  have hd : (fun u => ENNReal.ofReal (halfPlanePoisson x y (-a + u))) =
      (fun u => ENNReal.ofReal (halfPlanePoisson (a + x) y u)) := by
    funext u
    rw [show -a + u = u - a by ring, halfPlanePoisson_translate]
  rw [hd] at h
  exact h

/-- Positive dilation covariance, including the inverse Jacobian. -/
theorem halfPlanePoisson_dilation (x y a u : ℝ) :
    dilatedBoundaryDensity a (halfPlanePoisson x y) u =
      halfPlanePoisson (Real.exp a * x) (Real.exp a * y) u := by
  unfold dilatedBoundaryDensity halfPlanePoisson
  rw [Real.exp_neg]
  have ha := Real.exp_pos a
  have hid : (u - Real.exp a * x) ^ 2 + (Real.exp a * y) ^ 2 =
      (Real.exp a) ^ 2 * (((Real.exp a)⁻¹ * u - x) ^ 2 + y ^ 2) := by
    field_simp
  rw [hid]
  field_simp

/-- Boundary dilation transports the normalized Poisson measure to the
correspondingly dilated interior point. -/
theorem halfPlanePoissonMeasure_dilation (x y a : ℝ) :
    Measure.map (fun u : ℝ => Real.exp a * u) (halfPlanePoissonMeasure x y) =
      halfPlanePoissonMeasure (Real.exp a * x) (Real.exp a * y) := by
  rw [halfPlanePoissonMeasure, dilatedBoundaryDensity_map _ _ (measurable_halfPlanePoisson x y)]
  congr 1
  funext u
  rw [halfPlanePoisson_dilation]

/-- The Poisson measure at an actual upper-half-plane point. -/
def poissonBoundaryMeasure (z : UpperHalfPlane) : Measure ℝ := halfPlanePoissonMeasure z.re z.im

theorem poissonBoundaryMeasure_probability (z : UpperHalfPlane) :
    IsProbabilityMeasure (poissonBoundaryMeasure z) := halfPlanePoissonMeasure_probability z.re z.im_pos

end Singularity
