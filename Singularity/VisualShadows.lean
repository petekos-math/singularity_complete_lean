import Singularity.VerticalShadowLemma
import Singularity.HyperbolicAxisNormalization

/-!
# Visual shadows at arbitrary basepoints

An oriented hyperbolic axis transports the explicit vertical cap. The parameter
r is positive and decreasing it enlarges the cap. The definition includes a
choice of axis; all mass estimates are independent of that choice. No
identification with a random-walk shadow is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

/-- Choose an oriented axis carrying i and its upward ray point to z and w. -/
def visualShadowAxis (z w : ℍ) : SL(2, ℝ) := (exists_oriented_hyperbolic_axis z w).choose

/-- The chosen axis sends both specified interior points to their targets. -/
theorem visualShadowAxis_spec (z w : ℍ) :
    visualShadowAxis z w • UpperHalfPlane.I = z ∧
      visualShadowAxis z w • verticalHeightRay UpperHalfPlane.I (dist z w) = w :=
  (exists_oriented_hyperbolic_axis z w).choose_spec

/-- A visual shadow obtained by transporting the explicit vertical cap. -/
def visualShadow (z w : ℍ) (r : ℝ) : Set (OnePoint ℝ) :=
  (fun ξ : OnePoint ℝ => visualShadowAxis z w • ξ) '' verticalVisualShadow (dist z w) r

/-- Every transported visual shadow is open. -/
theorem isOpen_visualShadow (z w : ℍ) (r : ℝ) : IsOpen (visualShadow z w r) :=
  isOpenMap_smul (visualShadowAxis z w) _ (isOpen_verticalVisualShadow _ _)

/-- Exact covariance of visual mass under the image of a measurable boundary set. -/
theorem compactPoissonMeasure_smul_image (a : SL(2, ℝ)) (z : ℍ)
    {S : Set (OnePoint ℝ)} (hS : MeasurableSet S) :
    compactPoissonMeasure (a • z) ((fun ξ : OnePoint ℝ => a • ξ) '' S) = compactPoissonMeasure z S := by
  rw [← compactPoissonMeasure_covariance,
    Measure.map_apply (measurable_const_smul a)
      ((measurableEmbedding_const_smul (α := OnePoint ℝ) a).measurableSet_image.mpr hS),
    preimage_image_eq _ (show Function.Injective (fun ξ : OnePoint ℝ => a • ξ) from
      (MeasurableEquiv.smul a).injective)]

/-- The mass at the basepoint is exactly the normalized vertical-shadow mass. -/
theorem visualShadow_mass_at_base (z w : ℍ) (r : ℝ) :
    compactPoissonMeasure z (visualShadow z w r) =
      compactPoissonMeasure UpperHalfPlane.I (verticalVisualShadow (dist z w) r) := by
  rw [visualShadow]
  nth_rw 1 [← (visualShadowAxis_spec z w).1]
  exact compactPoissonMeasure_smul_image _ _ (isOpen_verticalVisualShadow _ _).measurableSet

/-- Viewed from its center, every shadow has the same positive mass. -/
theorem visualShadow_mass_at_center (z w : ℍ) (r : ℝ) :
    compactPoissonMeasure w (visualShadow z w r) = verticalShadowMass r := by
  change compactPoissonMeasure w
    ((fun ξ : OnePoint ℝ => visualShadowAxis z w • ξ) '' verticalVisualShadow (dist z w) r) = _
  nth_rw 1 [← (visualShadowAxis_spec z w).2]
  rw [compactPoissonMeasure_smul_image _ _ (isOpen_verticalVisualShadow _ _).measurableSet]
  exact verticalVisualShadow_mass_at_center _ _

/-- The visual shadow lemma at arbitrary basepoints, with fully explicit constants. -/
theorem visualShadow_mass_bounds (z w : ℍ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (Real.exp (-dist z w)) * verticalShadowMass r ≤
        compactPoissonMeasure z (visualShadow z w r) ∧
      compactPoissonMeasure z (visualShadow z w r) ≤
        ENNReal.ofReal (verticalShadowFactor r * Real.exp (-dist z w)) * verticalShadowMass r := by
  rw [visualShadow_mass_at_base]
  exact verticalVisualShadow_mass_bounds dist_nonneg hr

/-- Pulling a shadow back by a projective group element gives a set of fixed
positive visual mass. The statement needs no discreteness or compact quotient. -/
theorem projective_visualShadow_preimage_mass (g : PSL(2, ℝ)) (z : ℍ) (r : ℝ) :
    compactPoissonMeasure z ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r) =
      verticalShadowMass r := by
  rw [← Measure.map_apply (measurable_const_smul g) (isOpen_visualShadow _ _ _).measurableSet,
    compactPoissonMeasure_projective_covariance, visualShadow_mass_at_center]

end Singularity
