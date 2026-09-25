import Singularity.CurrentComparison
import Singularity.LiouvilleFourier
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Logarithmic coordinates for boundary measures

The maps t ↦ exp(t) and t ↦ -exp(t) parametrize the positive and negative
boundary half-lines. The Jacobian identities below are identities of measures,
so they apply even to currents with infinite mass.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Singularity

/-- A density pulled back along a measurable map commutes with pushforward. -/
theorem map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (m : Measure X) (w : Y → ℝ≥0∞)
    (hw : Measurable w) :
    Measure.map f (m.withDensity (w ∘ f)) = (Measure.map f m).withDensity w := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hf, lintegral_withDensity_eq_lintegral_mul _ (hw.comp hf)
      (show Measurable (fun x => h (f x)) from hh.comp hf),
    lintegral_withDensity_eq_lintegral_mul _ hw hh, lintegral_map (hw.mul hh) hf]
  rfl

/-- Exponential coordinates transport exp(t) dt to Lebesgue measure on (0,∞). -/
theorem exp_jacobian_map :
    Measure.map Real.exp (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t))) =
      volume.restrict (Ioi (0 : ℝ)) := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh Real.measurable_exp,
    lintegral_withDensity_eq_lintegral_mul _ Real.measurable_exp.ennreal_ofReal
      (show Measurable (fun x => h (Real.exp x)) from hh.comp Real.measurable_exp)]
  simpa only [image_univ, Real.range_exp, Measure.restrict_univ,
    abs_of_pos (Real.exp_pos _), Pi.mul_apply] using
    (lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn h).symm

/-- The negative exponential parametrizes precisely the negative half-line. -/
theorem range_neg_exp : range (fun t : ℝ => -Real.exp t) = Iio 0 := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact neg_neg_of_pos (Real.exp_pos t)
  · intro hx
    exact ⟨Real.log (-x), by simp only [Real.exp_log (neg_pos.mpr hx), neg_neg]⟩

/-- Negative exponential coordinates have absolute Jacobian exp(t). -/
theorem neg_exp_jacobian_map :
    Measure.map (fun t : ℝ => -Real.exp t)
      (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t))) =
      volume.restrict (Iio (0 : ℝ)) := by
  apply Measure.ext_of_lintegral
  intro h hh
  have hm : Measurable (fun t : ℝ => -Real.exp t) := Real.measurable_exp.neg
  rw [lintegral_map hh hm,
    lintegral_withDensity_eq_lintegral_mul _ Real.measurable_exp.ennreal_ofReal
      (show Measurable (fun x => h (-Real.exp x)) from hh.comp hm)]
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp t) (-Real.exp x) x :=
    (Real.hasDerivAt_exp x).neg
  simpa only [image_univ, range_neg_exp, Measure.restrict_univ, abs_neg,
    abs_of_pos (Real.exp_pos _), Pi.mul_apply] using
    (lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
      (fun x _ => (hd x).hasDerivWithinAt)
      (neg_injective.comp Real.exp_injective).injOn h).symm

/-- Coordinates for an ordered boundary pair on opposite sides of zero. -/
def logBoundaryPair (z : ℝ × ℝ) : ℝ × ℝ := (-Real.exp z.1, Real.exp z.2)

theorem measurable_logBoundaryPair : Measurable logBoundaryPair := by
  exact (Real.measurable_exp.neg.comp measurable_fst).prodMk
    (Real.measurable_exp.comp measurable_snd)

/-- The two-dimensional Jacobian is exp(s) exp(t). -/
theorem logBoundaryPair_jacobian_map :
    Measure.map logBoundaryPair ((volume.prod volume).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2))) =
    (volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : Measurable (fun t : ℝ => -Real.exp t) := Real.measurable_exp.neg
  have h := Measure.map_prod_map
    (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t)))
    (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t)))
    hm Real.measurable_exp
  rw [neg_exp_jacobian_map, exp_jacobian_map,
    prod_withDensity Real.measurable_exp.ennreal_ofReal Real.measurable_exp.ennreal_ofReal] at h
  have hf : Prod.map (fun t : ℝ => -Real.exp t) Real.exp = logBoundaryPair := by
    funext z
    rfl
  rw [hf] at h
  simpa only [ENNReal.ofReal_mul (Real.exp_pos _).le] using h.symm

/-- Weighted change of variables for the two boundary half-lines. -/
theorem logBoundaryPair_weighted_map (w : ℝ × ℝ → ℝ≥0∞) (hw : Measurable w) :
    Measure.map logBoundaryPair ((volume.prod volume).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2) *
        w (logBoundaryPair z))) =
    ((volume.restrict (Iio (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))).withDensity w := by
  have h := map_withDensity_comp logBoundaryPair measurable_logBoundaryPair
    ((volume.prod volume).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2))) w hw
  rw [logBoundaryPair_jacobian_map, ← withDensity_mul _ (by fun_prop)
    (hw.comp measurable_logBoundaryPair)] at h
  exact h

/-- The Jacobian times the classical Liouville density is the kernel already
used in the Fourier calculation. -/
theorem logBoundaryPair_liouville_density (s t : ℝ) :
    Real.exp s * Real.exp t * (1 / ((-Real.exp s) - Real.exp t) ^ 2) =
      liouvilleKernel (s - t) := by
  unfold liouvilleKernel
  rw [neg_sub, Real.exp_sub]
  have hs := Real.exp_pos s
  have ht := Real.exp_pos t
  rw [show (-Real.exp s - Real.exp t) ^ 2 = (Real.exp s + Real.exp t) ^ 2 by ring]
  have hr : 1 + Real.exp t / Real.exp s = (Real.exp s + Real.exp t) / Real.exp s := by
    field_simp
  rw [hr, div_pow, div_div]
  field_simp [ne_of_gt hs, ne_of_gt (add_pos hs ht)]

/-- The classical Liouville density in the finite real boundary chart. -/
def realLiouvilleDensity (z : ℝ × ℝ) : ℝ := 1 / (z.1 - z.2) ^ 2

theorem measurable_realLiouvilleDensity : Measurable realLiouvilleDensity := by
  unfold realLiouvilleDensity
  fun_prop

/-- Pushing forward the cosh-kernel measure in logarithmic coordinates gives
the classical Liouville current restricted to opposite half-lines. -/
theorem logBoundaryPair_liouville_map :
    Measure.map logBoundaryPair ((volume.prod volume).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal (liouvilleKernel (z.1 - z.2)))) =
    ((volume.restrict (Iio (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))).withDensity
      (fun z => ENNReal.ofReal (realLiouvilleDensity z)) := by
  have h := logBoundaryPair_weighted_map
    (fun z => ENNReal.ofReal (realLiouvilleDensity z))
    measurable_realLiouvilleDensity.ennreal_ofReal
  have hd : (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2) *
      ENNReal.ofReal (realLiouvilleDensity (logBoundaryPair z))) =
      (fun z => ENNReal.ofReal (liouvilleKernel (z.1 - z.2))) := by
    funext z
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact congrArg ENNReal.ofReal (logBoundaryPair_liouville_density z.1 z.2)
  rw [hd] at h
  exact h

/-- The logarithmic chart is a measurable embedding, so equality of its
pushforward measures implies equality of the original measures. -/
theorem measurableEmbedding_logBoundaryPair : MeasurableEmbedding logBoundaryPair := by
  have he := Real.isOpenEmbedding_exp.measurableEmbedding
  have hn : MeasurableEmbedding (fun t : ℝ => -Real.exp t) :=
    (Homeomorph.neg ℝ).measurableEmbedding.comp he
  have h := hn.prodMap he
  have hf : Prod.map (fun t : ℝ => -Real.exp t) Real.exp = logBoundaryPair := by
    funext z
    rfl
  rwa [hf] at h

/-- Null sets for product Lebesgue measure remain null on logarithmic pullback. -/
theorem quasiMeasurePreserving_logBoundaryPair :
    Measure.QuasiMeasurePreserving logBoundaryPair (volume.prod volume) (volume.prod volume) := by
  have hp : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, 0 < Real.exp z.1 * Real.exp z.2 :=
    Filter.Eventually.of_forall (fun z => mul_pos (Real.exp_pos z.1) (Real.exp_pos z.2))
  have hac := ((positive_real_weight_measureClass (volume.prod volume)
    (fun z : ℝ × ℝ => Real.exp z.1 * Real.exp z.2) (by fun_prop) hp).2).map
      measurable_logBoundaryPair
  rw [logBoundaryPair_jacobian_map, Measure.prod_restrict] at hac
  exact ⟨measurable_logBoundaryPair, hac.trans Measure.absolutelyContinuous_restrict⟩

/-- The density identity forced by a scalar Liouville-current identity on the
opposite boundary half-lines, with both logarithmic Jacobians included. -/
theorem log_current_density_identity (F : ℝ × ℝ → ℝ) (hF : Measurable F)
    (hpF : ∀ z, 0 ≤ F z) (c : ℝ≥0∞)
    (heq : ((volume.restrict (Iio (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))).withDensity
        (fun z => ENNReal.ofReal (F z)) =
      c • ((volume.restrict (Iio (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))).withDensity
        (fun z => ENNReal.ofReal (realLiouvilleDensity z))) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      Real.exp z.1 * Real.exp z.2 * F (logBoundaryPair z) =
        c.toReal / (4 * Real.cosh ((z.1 - z.2) / 2) ^ 2) := by
  have hmap := logBoundaryPair_weighted_map (fun z => ENNReal.ofReal (F z)) hF.ennreal_ofReal
  have hd : (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2) *
      ENNReal.ofReal (F (logBoundaryPair z))) =
      (fun z => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2 * F (logBoundaryPair z))) := by
    funext z
    exact (ENNReal.ofReal_mul (by positivity)).symm
  rw [hd, heq, ← logBoundaryPair_liouville_map,
    ← Measure.map_smul c measurable_logBoundaryPair.aemeasurable] at hmap
  have heq' := measurableEmbedding_logBoundaryPair.map_injective hmap
  have hid := real_density_eq_of_measure_eq_smul (volume.prod volume)
    (fun z => Real.exp z.1 * Real.exp z.2 * F (logBoundaryPair z))
    (fun z => liouvilleKernel (z.1 - z.2))
    (((Real.measurable_exp.comp measurable_fst).mul
      (Real.measurable_exp.comp measurable_snd)).mul (hF.comp measurable_logBoundaryPair))
    (by unfold liouvilleKernel; fun_prop)
    (Filter.Eventually.of_forall (fun z =>
      mul_nonneg (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le (hpF _)))
    (Filter.Eventually.of_forall (fun z => by unfold liouvilleKernel; positivity)) c heq'
  filter_upwards [hid] with z hz
  rw [hz, liouvilleKernel_eq_cosh]
  ring

/-- With boundary densities f and g, a weighted-product current identity gives
the precise scalar identity in logarithmic coordinates. -/
theorem log_weightedProduct_current_density_identity
    (f g : ℝ → ℝ) (K : ℝ × ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hK : Measurable K)
    (hpf : ∀ x, 0 ≤ f x) (hpg : ∀ y, 0 ≤ g y) (hpK : ∀ z, 0 ≤ K z)
    (c : ℝ≥0∞)
    (heq : (((volume.restrict (Iio (0 : ℝ))).withDensity
      (fun x => ENNReal.ofReal (f x))).prod
      ((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal (g y)))).withDensity
        (fun z => ENNReal.ofReal (K z)) =
      c • ((volume.restrict (Iio (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))).withDensity
        (fun z => ENNReal.ofReal (realLiouvilleDensity z))) :
    ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
      (Real.exp z.1 * f (-Real.exp z.1)) * (Real.exp z.2 * g (Real.exp z.2)) *
        K (logBoundaryPair z) = c.toReal / (4 * Real.cosh ((z.1 - z.2) / 2) ^ 2) := by
  rw [weightedProduct_real_density _ _ f g K hf hg hK hpf hpg] at heq
  have h := log_current_density_identity (fun z => f z.1 * g z.2 * K z)
    (by fun_prop) (fun z => mul_nonneg (mul_nonneg (hpf _) (hpg _)) (hpK _)) c heq
  filter_upwards [h] with z hz
  rw [← hz]
  simp only [logBoundaryPair]
  ring

end Singularity
