import Singularity.WeightedCurrent
import Singularity.ErgodicCurrent

/-!
# Measure classes and scalar density identities for currents

Positive weights preserve measure classes. Combining this with absolute
continuity of the boundary measures supplies the measure-comparison hypothesis
in the ergodic uniqueness theorem. Equality of weighted measures then gives the
scalar density identity, without a finite-total-mass assumption.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Singularity

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable, almost everywhere positive real weight preserves the measure class. -/
theorem positive_real_weight_measureClass (m : Measure X) (w : X → ℝ)
    (hw : Measurable w) (hp : ∀ᵐ x ∂m, 0 < w x) :
    m.withDensity (fun x => ENNReal.ofReal (w x)) ≪ m ∧
      m ≪ m.withDensity (fun x => ENNReal.ofReal (w x)) := by
  refine ⟨withDensity_absolutelyContinuous _ _,
    withDensity_absolutelyContinuous' hw.ennreal_ofReal.aemeasurable ?_⟩
  filter_upwards [hp] with x hx
  exact ne_of_gt (ENNReal.ofReal_pos.mpr hx)

/-- A positive weight over a nonzero measure gives a nonzero measure. -/
theorem positive_real_weight_ne_zero (m : Measure X) [NeZero m] (w : X → ℝ)
    (hw : Measurable w) (hp : ∀ᵐ x ∂m, 0 < w x) :
    m.withDensity (fun x => ENNReal.ofReal (w x)) ≠ 0 := by
  intro hz
  have h := (positive_real_weight_measureClass m w hw hp).2
  rw [hz] at h
  exact NeZero.ne m (Measure.absolutelyContinuous_zero_iff.mp h)

/-- Absolute continuity of each boundary measure gives absolute continuity of
its weighted product relative to any positive reference-product density. -/
theorem weightedProduct_absolutelyContinuous
    (μ μ₀ : Measure X) (ν ν₀ : Measure Y) [SFinite ν] [SFinite ν₀]
    (hμ : μ ≪ μ₀) (hν : ν ≪ ν₀) (K L : X × Y → ℝ)
    (hL : Measurable L) (hpL : ∀ᵐ z ∂μ₀.prod ν₀, 0 < L z) :
    (μ.prod ν).withDensity (fun z => ENNReal.ofReal (K z)) ≪
      (μ₀.prod ν₀).withDensity (fun z => ENNReal.ofReal (L z)) :=
  (withDensity_absolutelyContinuous _ _).trans
    ((hμ.prod hν).trans (positive_real_weight_measureClass _ L hL hpL).2)

/-- Equivalent marginals and positive kernels give equivalent currents. -/
theorem weightedProduct_measureClass
    (μ μ₀ : Measure X) (ν ν₀ : Measure Y) [SFinite ν] [SFinite ν₀]
    (hμ : μ ≪ μ₀) (hμ' : μ₀ ≪ μ) (hν : ν ≪ ν₀) (hν' : ν₀ ≪ ν)
    (K L : X × Y → ℝ) (hK : Measurable K) (hL : Measurable L)
    (hpK : ∀ᵐ z ∂μ.prod ν, 0 < K z) (hpL : ∀ᵐ z ∂μ₀.prod ν₀, 0 < L z) :
    (μ.prod ν).withDensity (fun z => ENNReal.ofReal (K z)) ≪
      (μ₀.prod ν₀).withDensity (fun z => ENNReal.ofReal (L z)) ∧
    (μ₀.prod ν₀).withDensity (fun z => ENNReal.ofReal (L z)) ≪
      (μ.prod ν).withDensity (fun z => ENNReal.ofReal (K z)) :=
  ⟨weightedProduct_absolutelyContinuous μ μ₀ ν ν₀ hμ hν K L hL hpL,
    weightedProduct_absolutelyContinuous μ₀ μ ν₀ ν hμ' hν' L K hK hpK⟩

/-- Scalar equality of measures with nonnegative real densities implies the
corresponding almost-everywhere real identity. -/
theorem real_density_eq_of_measure_eq_smul (m : Measure X) [SigmaFinite m]
    (F L : X → ℝ) (hF : Measurable F) (hL : Measurable L)
    (hpF : ∀ᵐ x ∂m, 0 ≤ F x) (hpL : ∀ᵐ x ∂m, 0 ≤ L x) (c : ℝ≥0∞)
    (heq : m.withDensity (fun x => ENNReal.ofReal (F x)) =
      c • m.withDensity (fun x => ENNReal.ofReal (L x))) :
    ∀ᵐ x ∂m, F x = c.toReal * L x := by
  rw [← withDensity_smul c hL.ennreal_ofReal] at heq
  have h := (withDensity_eq_iff_of_sigmaFinite hF.ennreal_ofReal.aemeasurable
    (measurable_const.mul hL.ennreal_ofReal).aemeasurable).mp heq
  filter_upwards [h, hpF, hpL] with x hx hxF hxL
  have ht := congrArg ENNReal.toReal hx
  simpa only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hxF, ENNReal.toReal_ofReal hxL] using ht

/-- Boundary densities and a real kernel multiply to give the density of the
weighted product with respect to the original product reference measure. -/
theorem weightedProduct_real_density (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (f : X → ℝ) (g : Y → ℝ) (K : X × Y → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hK : Measurable K)
    (hpf : ∀ x, 0 ≤ f x) (hpg : ∀ y, 0 ≤ g y) :
    ((μ.withDensity (fun x => ENNReal.ofReal (f x))).prod
      (ν.withDensity (fun y => ENNReal.ofReal (g y)))).withDensity
      (fun z => ENNReal.ofReal (K z)) =
    (μ.prod ν).withDensity (fun z => ENNReal.ofReal (f z.1 * g z.2 * K z)) := by
  rw [prod_withDensity hf.ennreal_ofReal hg.ennreal_ofReal, ← withDensity_mul]
  · congr 1
    funext z
    simp only [Pi.mul_apply, ENNReal.ofReal_mul (hpf z.1),
      ENNReal.ofReal_mul (mul_nonneg (hpf z.1) (hpg z.2))]
  · exact (hf.ennreal_ofReal.comp measurable_fst).mul (hg.ennreal_ofReal.comp measurable_snd)
  · exact hK.ennreal_ofReal

/-- Under ergodicity and invariance, positive real densities are proportional
almost everywhere by a strictly positive real constant. -/
theorem ergodic_current_density_identity {G : Type*} [Group G] [MulAction G X]
    [MeasurableConstSMul G X] (m : Measure X) [SigmaFinite m] [NeZero m]
    (F L : X → ℝ) (hF : Measurable F) (hL : Measurable L)
    (hpF : ∀ᵐ x ∂m, 0 < F x) (hpL : ∀ᵐ x ∂m, 0 < L x)
    [ErgodicSMul G X (m.withDensity (fun x => ENNReal.ofReal (L x)))]
    (hi : ∀ g : G, Measure.map (fun x => g • x)
      (m.withDensity (fun x => ENNReal.ofReal (F x))) =
      m.withDensity (fun x => ENNReal.ofReal (F x))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂m, F x = c * L x := by
  let : NeZero (m.withDensity (fun x => ENNReal.ofReal (F x))) :=
    ⟨positive_real_weight_ne_zero m F hF hpF⟩
  let : NeZero (m.withDensity (fun x => ENNReal.ofReal (L x))) :=
    ⟨positive_real_weight_ne_zero m L hL hpL⟩
  have hac := (positive_real_weight_measureClass m F hF hpF).1.trans
    (positive_real_weight_measureClass m L hL hpL).2
  obtain ⟨c, hc, hct, heq⟩ := invariantMeasure_eq_pos_finite_smul_of_maps (G := G)
    (m.withDensity (fun x => ENNReal.ofReal (L x)))
    (m.withDensity (fun x => ENNReal.ofReal (F x))) hi hac
  exact ⟨c.toReal, ENNReal.toReal_pos hc.ne' hct.ne,
    real_density_eq_of_measure_eq_smul m F L hF hL
      (hpF.mono fun _ h => h.le) (hpL.mono fun _ h => h.le) c heq⟩

end Singularity
