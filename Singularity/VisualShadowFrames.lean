import Singularity.VisualShadows
import Singularity.DilationNorthSouth
import Singularity.DilationGeometry
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Compact frames for inverse visual shadows

After pulling a visual shadow back by g and undoing its height dilation, its
complement is the image of [-r,r] by a frame sending i to the fixed basepoint.
Properness of the SL₂ action makes this family of frames compact.
-/

noncomputable section
open Set Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology

namespace Singularity

/-- The diagonal dilation carries i to the chosen vertical ray point. -/
theorem dilationMatrix_smul_I_verticalHeightRay (t : ℝ) :
    dilationMatrix t • UpperHalfPlane.I = verticalHeightRay UpperHalfPlane.I t := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simpa [verticalHeightRay] using dilationMatrix_smul_re t UpperHalfPlane.I
  · simpa [verticalHeightRay] using dilationMatrix_smul_im t UpperHalfPlane.I

/-- The complement of a vertical cap is the dilation of a fixed real interval. -/
theorem verticalVisualShadow_compl_dilation (t r : ℝ) :
    (verticalVisualShadow t r)ᶜ =
      (fun x : ℝ => dilationMatrix t • (x : OnePoint ℝ)) '' Icc (-r) r := by
  simp only [verticalVisualShadow, compl_compl, compactBoundary_dilation_coe]
  have hi := image_mul_left_Icc' (Real.exp_pos t) (-r) r
  rw [mul_neg, ← neg_mul] at hi
  rw [← hi, image_image]

/-- The normalized frame describing the complement of the inverse shadow. -/
def inverseVisualShadowFrame (g : SL(2, ℝ)) (z : ℍ) : SL(2, ℝ) :=
  g⁻¹ * visualShadowAxis z (g • z) * dilationMatrix (dist z (g • z))

/-- All normalized inverse-shadow frames lie in a single orbit-map fiber. -/
theorem inverseVisualShadowFrame_smul_I (g : SL(2, ℝ)) (z : ℍ) :
    inverseVisualShadowFrame g z • UpperHalfPlane.I = z := by
  rw [inverseVisualShadowFrame, mul_smul, mul_smul,
    dilationMatrix_smul_I_verticalHeightRay, (visualShadowAxis_spec z (g • z)).2,
    inv_smul_smul]

/-- Exact interval description of the inverse-shadow complement. -/
theorem inverse_visualShadow_compl_frame (g : SL(2, ℝ)) (z : ℍ) (r : ℝ) :
    (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r)ᶜ) =
      (fun x : ℝ => inverseVisualShadowFrame g z • (x : OnePoint ℝ)) '' Icc (-r) r := by
  have hp (S : Set (OnePoint ℝ)) :
      (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' S = (fun ξ : OnePoint ℝ => g⁻¹ • ξ) '' S := by
    ext ξ
    constructor
    · intro h
      exact ⟨g • ξ, h, inv_smul_smul g ξ⟩
    · rintro ⟨η, hη, rfl⟩
      simpa only [mem_preimage, smul_inv_smul] using hη
  rw [← preimage_compl, visualShadow,
    ← image_compl_eq (show Function.Bijective (fun ξ : OnePoint ℝ => visualShadowAxis z (g • z) • ξ) from
      (MeasurableEquiv.smul (visualShadowAxis z (g • z))).bijective),
    verticalVisualShadow_compl_dilation, hp]
  simp only [image_image, inverseVisualShadowFrame, mul_smul]

/-- Properness of the interior action makes the normalized frame fiber compact. -/
theorem isCompact_visualShadowFrame_fiber (z : ℍ) :
    IsCompact {a : SL(2, ℝ) | a • UpperHalfPlane.I = z} := by
  exact UpperHalfPlane.isProperMap_smul_I.isCompact_preimage (isCompact_singleton (x := z))

/-- Every sequence of inverse-shadow frames has a convergent subsequence,
without any escape or cocompactness assumption. -/
theorem inverseVisualShadowFrame_subsequence (g : ℕ → SL(2, ℝ)) (z : ℍ) :
    ∃ a : SL(2, ℝ), a • UpperHalfPlane.I = z ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => inverseVisualShadowFrame (g (φ n)) z) atTop (𝓝 a) := by
  let : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))
  let : FirstCountableTopology SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.firstCountableTopology
  exact (isCompact_visualShadowFrame_fiber z).tendsto_subseq
    (fun n => inverseVisualShadowFrame_smul_I (g n) z)

end Singularity
