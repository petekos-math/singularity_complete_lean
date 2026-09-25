import Singularity.FourierTranslation
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Convolution by an L¹ kernel on the actual L² space

The operator is defined as the Bochner integral of translated L² vectors.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace Singularity

/-- Translation is strongly continuous on L². -/
theorem realTranslation_continuous (f : RealLineL2) : Continuous (fun a => realTranslation a f) := by
  let g : C(ℝ × ℝ, ℝ) := ⟨fun p => p.2 - p.1, continuous_snd.sub continuous_fst⟩
  exact continuous_const.compMeasurePreservingLp g.curry.continuous
    (fun a => measurePreserving_sub_right volume a) ENNReal.ofNat_ne_top

/-- An L¹ kernel gives an integrable family of translated L² vectors. -/
theorem convolutionL2_integrable {k : ℝ → ℂ} (hk : Integrable k) (f : RealLineL2) :
    Integrable (fun t => k t • realTranslation t f) := by
  apply (hk.norm.mul_const ‖f‖).mono'
    (hk.aestronglyMeasurable.smul (realTranslation_continuous f).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t => by
    change ‖k t • realTranslation t f‖ ≤ ‖k t‖ * ‖f‖
    rw [norm_smul, (realTranslation t).norm_map])

/-- Convolution before bundling its continuity. -/
def convolutionL2Linear (k : ℝ → ℂ) (hk : Integrable k) : RealLineL2 →ₗ[ℂ] RealLineL2 where
  toFun f := ∫ t, k t • realTranslation t f
  map_add' f g := by
    simp only [map_add, smul_add]
    exact integral_add (convolutionL2_integrable hk f) (convolutionL2_integrable hk g)
  map_smul' c f := by
    simp only [map_smul, smul_comm (k _) c]
    exact integral_smul c _

/-- Young's L¹–L² norm bound, directly from the Bochner integral. -/
theorem convolutionL2Linear_bound (k : ℝ → ℂ) (hk : Integrable k) (f : RealLineL2) :
    ‖convolutionL2Linear k hk f‖ ≤ (∫ t, ‖k t‖) * ‖f‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp only [norm_smul, (realTranslation _).norm_map, integral_mul_const]

/-- The bounded convolution operator. -/
def convolutionL2 (k : ℝ → ℂ) (hk : Integrable k) : RealLineL2 →L[ℂ] RealLineL2 :=
  (convolutionL2Linear k hk).mkContinuous (∫ t, ‖k t‖) (convolutionL2Linear_bound k hk)

/-- Its quantitative norm bound. -/
theorem convolutionL2_norm_le (k : ℝ → ℂ) (hk : Integrable k) :
    ‖convolutionL2 k hk‖ ≤ ∫ t, ‖k t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun _ => norm_nonneg _))
  exact convolutionL2Linear_bound k hk

/-- A weak integral formula valid for arbitrary L² inputs and test vectors. -/
theorem convolutionL2_inner (k : ℝ → ℂ) (hk : Integrable k) (f h : RealLineL2) :
    inner ℂ h (convolutionL2 k hk f) = ∫ t, k t * inner ℂ h (realTranslation t f) := by
  change inner ℂ h (∫ t, k t • realTranslation t f) = _
  rw [← integral_inner (convolutionL2_integrable hk f)]
  simp only [inner_smul_right]

/-- Fourier covariance passes through the Bochner integral. -/
theorem fourier_convolutionL2_integral (k : ℝ → ℂ) (hk : Integrable k) (f : RealLineL2) :
    Lp.fourierTransformₗᵢ ℝ ℂ (convolutionL2 k hk f) =
      ∫ t, k t • frequencyModulation t (Lp.fourierTransformₗᵢ ℝ ℂ f) := by
  change (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    (∫ t, k t • realTranslation t f) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ (convolutionL2_integrable hk f)]
  simp only [map_smul]
  congr 1
  funext t
  exact congrArg (fun v : RealLineL2 => k t • v) (fourier_realTranslation t f)

end Singularity
