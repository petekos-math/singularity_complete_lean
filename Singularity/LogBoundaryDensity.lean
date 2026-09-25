import Singularity.LogBoundaryMeasure
import Singularity.PoissonAnalysis
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Logarithmic boundary densities

For a real boundary density f, the positive and negative logarithmic densities
are exp(t) f(exp(t)) and exp(t) f(-exp(t)). We prove their measure identities,
subprobability mass bounds, and covariance under genuine dilation pushforwards.
No random-walk hitting measure is assumed to have been constructed here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

/-- The logarithmic density on the side selected by ε = 1 or ε = -1. -/
def logBoundaryDensity (ε : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp t * f (ε * Real.exp t)

theorem measurable_logBoundaryDensity (ε : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable (logBoundaryDensity ε f) := by
  unfold logBoundaryDensity
  fun_prop

theorem logBoundaryDensity_nonneg (ε : ℝ) (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) (t : ℝ) :
    0 ≤ logBoundaryDensity ε f t := mul_nonneg (Real.exp_pos t).le (hf _)

/-- The positive-side logarithmic density is the actual pullback of the
restricted boundary measure. -/
theorem logBoundaryDensity_positive_map (f : ℝ → ℝ) (hf : Measurable f) :
    Measure.map Real.exp (volume.withDensity
      (fun t => ENNReal.ofReal (logBoundaryDensity 1 f t))) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (f x)) := by
  have h := map_withDensity_comp Real.exp Real.measurable_exp
    (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t)))
    (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal
  rw [exp_jacobian_map, ← withDensity_mul _ Real.measurable_exp.ennreal_ofReal
    (hf.ennreal_ofReal.comp Real.measurable_exp)] at h
  simpa only [logBoundaryDensity, one_mul, ENNReal.ofReal_mul (Real.exp_pos _).le,
    Pi.mul_def, Function.comp_def] using h

/-- The negative-side logarithmic density includes the absolute Jacobian,
which has the same positive value exp(t). -/
theorem logBoundaryDensity_negative_map (f : ℝ → ℝ) (hf : Measurable f) :
    Measure.map (fun t : ℝ => -Real.exp t) (volume.withDensity
      (fun t => ENNReal.ofReal (logBoundaryDensity (-1) f t))) =
      (volume.restrict (Iio (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (f x)) := by
  have hm : Measurable (fun t : ℝ => -Real.exp t) := Real.measurable_exp.neg
  have h := map_withDensity_comp (fun t : ℝ => -Real.exp t) hm
    (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t)))
    (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal
  rw [neg_exp_jacobian_map, ← withDensity_mul _ Real.measurable_exp.ennreal_ofReal
    (hf.ennreal_ofReal.comp hm)] at h
  simpa only [logBoundaryDensity, neg_one_mul, ENNReal.ofReal_mul (Real.exp_pos _).le,
    Pi.mul_def, Function.comp_def] using h

/-- A measurable nonnegative subprobability density is integrable and has
Bochner integral at most one. -/
theorem real_density_integrable_of_mass_le_one (k : ℝ → ℝ) (hk : Measurable k)
    (hp : ∀ t, 0 ≤ k t)
    (hmass : (volume.withDensity (fun t => ENNReal.ofReal (k t))) univ ≤ 1) :
    Integrable k ∧ ∫ t, k t ≤ 1 := by
  have hp' : 0 ≤ᵐ[volume] k := Eventually.of_forall hp
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  have hint : Integrable k := ⟨hk.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hp').mpr (hmass.trans_lt ENNReal.one_lt_top)⟩
  refine ⟨hint, ENNReal.ofReal_le_one.mp ?_⟩
  rwa [ofReal_integral_eq_lintegral_ofReal hint hp']

/-- Restricting a boundary subprobability measure to either half-line and
passing to logarithmic coordinates preserves the mass bound. -/
theorem logBoundaryDensity_integrable_mass (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (f : ℝ → ℝ) (hf : Measurable f) (hp : ∀ x, 0 ≤ f x)
    (hmass : (volume.withDensity (fun x => ENNReal.ofReal (f x))) univ ≤ 1) :
    Integrable (logBoundaryDensity ε f) ∧ ∫ t, logBoundaryDensity ε f t ≤ 1 := by
  apply real_density_integrable_of_mass_le_one _ (measurable_logBoundaryDensity ε f hf)
    (logBoundaryDensity_nonneg ε f hp)
  rcases hε with rfl | rfl
  · have h := congrArg (fun m : Measure ℝ => m univ) (logBoundaryDensity_positive_map f hf)
    rw [Measure.map_apply Real.measurable_exp MeasurableSet.univ,
      preimage_univ, ← restrict_withDensity measurableSet_Ioi] at h
    rw [h]
    exact (Measure.restrict_le_self univ).trans hmass
  · have hm : Measurable (fun t : ℝ => -Real.exp t) := Real.measurable_exp.neg
    have h := congrArg (fun m : Measure ℝ => m univ) (logBoundaryDensity_negative_map f hf)
    rw [Measure.map_apply hm MeasurableSet.univ,
      preimage_univ, ← restrict_withDensity measurableSet_Iio] at h
    rw [h]
    exact (Measure.restrict_le_self univ).trans hmass

/-- The real density obtained by dilation of the boundary coordinate by exp(u). -/
def dilatedBoundaryDensity (u : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-u) * f (Real.exp (-u) * x)

theorem measurable_dilatedBoundaryDensity (u : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable (dilatedBoundaryDensity u f) := by
  unfold dilatedBoundaryDensity
  fun_prop

/-- Dilation of the real boundary measure has the stated density, including
its inverse Jacobian. -/
theorem dilatedBoundaryDensity_map (u : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    Measure.map (fun x : ℝ => Real.exp u * x)
      (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun x => ENNReal.ofReal (dilatedBoundaryDensity u f x)) := by
  have h := map_withDensity_equiv (MeasurableEquiv.mulLeft₀ (Real.exp u) (Real.exp_ne_zero u))
    volume (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal
  change Measure.map (fun x => Real.exp u * x) (volume.withDensity (fun x => ENNReal.ofReal (f x))) =
    (Measure.map (fun x => Real.exp u * x) volume).withDensity
      (fun x => ENNReal.ofReal (f ((Real.exp u)⁻¹ * x))) at h
  rw [Real.map_volume_mul_left (Real.exp_ne_zero u), withDensity_smul_measure,
    ← withDensity_smul _ (show Measurable (fun x => ENNReal.ofReal (f ((Real.exp u)⁻¹ * x))) from
      hf.ennreal_ofReal.comp (measurable_const_mul _))] at h
  simpa only [dilatedBoundaryDensity, Real.exp_neg, abs_of_pos (inv_pos.mpr (Real.exp_pos u)),
    Pi.smul_def, smul_eq_mul, ENNReal.ofReal_mul (inv_pos.mpr (Real.exp_pos u)).le] using h

/-- A boundary dilation becomes an ordinary translation of each logarithmic
density, on both sides of zero. -/
theorem logBoundaryDensity_dilation (ε u : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    logBoundaryDensity ε (dilatedBoundaryDensity u f) t = logBoundaryDensity ε f (t - u) := by
  have he : Real.exp t * Real.exp (-u) = Real.exp (t - u) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  unfold logBoundaryDensity dilatedBoundaryDensity
  rw [← he]
  rw [show Real.exp (-u) * (ε * Real.exp t) = ε * (Real.exp t * Real.exp (-u)) by ring]
  ring

/-- Both logarithmic parametrizations preserve null sets under pullback. -/
theorem quasiMeasurePreserving_signedExp (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => ε * Real.exp t) volume volume := by
  have hac := (positive_real_weight_measureClass volume Real.exp Real.measurable_exp
    (Eventually.of_forall Real.exp_pos)).2
  rcases hε with rfl | rfl
  · have h := hac.map Real.measurable_exp
    rw [exp_jacobian_map] at h
    simpa only [one_mul] using
      (show Measure.QuasiMeasurePreserving Real.exp volume volume from
        ⟨Real.measurable_exp, h.trans Measure.absolutelyContinuous_restrict⟩)
  · have hm : Measurable (fun t : ℝ => -Real.exp t) := Real.measurable_exp.neg
    have h := hac.map hm
    rw [neg_exp_jacobian_map] at h
    simpa only [neg_one_mul] using
      (show Measure.QuasiMeasurePreserving (fun t : ℝ => -Real.exp t) volume volume from
        ⟨hm, h.trans Measure.absolutelyContinuous_restrict⟩)

/-- The logarithmic density is independent almost everywhere of the chosen
representative of the real boundary density. -/
theorem logBoundaryDensity_congr_ae (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    logBoundaryDensity ε f =ᵐ[volume] logBoundaryDensity ε g := by
  filter_upwards [(quasiMeasurePreserving_signedExp ε hε).ae hfg] with t ht
  exact congrArg (fun v => Real.exp t * v) ht

/-- Nonnegative density representatives for equal measures agree almost everywhere. -/
theorem nonnegative_real_density_unique (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hpf : ∀ x, 0 ≤ f x) (hpg : ∀ x, 0 ≤ g x)
    (heq : volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g x))) : f =ᵐ[volume] g := by
  have h := real_density_eq_of_measure_eq_smul volume f g hf hg
    (Eventually.of_forall hpf) (Eventually.of_forall hpg) 1 (by simpa using heq)
  filter_upwards [h] with x hx
  simpa only [ENNReal.toReal_one, one_mul] using hx

/-- Any nonnegative density for a dilated boundary measure has the translated
logarithmic density. This is an a.e. statement about actual pushforward measures. -/
theorem logBoundaryDensity_translation_of_map (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (u : ℝ) (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hpf : ∀ x, 0 ≤ f x) (hpg : ∀ x, 0 ≤ g x)
    (hmap : volume.withDensity (fun x => ENNReal.ofReal (g x)) =
      Measure.map (fun x : ℝ => Real.exp u * x)
        (volume.withDensity (fun x => ENNReal.ofReal (f x)))) :
    logBoundaryDensity ε g =ᵐ[volume] fun t => logBoundaryDensity ε f (t - u) := by
  rw [dilatedBoundaryDensity_map u f hf] at hmap
  have heq := nonnegative_real_density_unique g (dilatedBoundaryDensity u f)
    hg (measurable_dilatedBoundaryDensity u f hf) hpg
    (fun x => mul_nonneg (Real.exp_pos (-u)).le (hpf _)) hmap
  exact (logBoundaryDensity_congr_ae ε hε heq).trans
    (Eventually.of_forall (logBoundaryDensity_dilation ε u f))

/-- A real-boundary Poisson bound gives the logarithmic Poisson bound on either
side; the center changes from x to -x on the negative side. -/
theorem logBoundaryDensity_poisson_domination (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (f : ℝ → ℝ) (x y B : ℝ) (hdom : ∀ u, f u ≤ B * halfPlanePoisson x y u) (t : ℝ) :
    logBoundaryDensity ε f t ≤ B * logPoissonProfile (ε * x) y t := by
  have h := mul_le_mul_of_nonneg_left (hdom (ε * Real.exp t)) (Real.exp_pos t).le
  change Real.exp t * f (ε * Real.exp t) ≤ _
  calc
    Real.exp t * f (ε * Real.exp t) ≤ Real.exp t * (B * halfPlanePoisson x y (ε * Real.exp t)) := h
    _ = B * (Real.exp t * halfPlanePoisson x y (ε * Real.exp t)) := by ring
    _ = B * logPoissonProfile (ε * x) y t := by
      rcases hε with rfl | rfl
      · simp only [one_mul, logPoissonProfile]
      · simp only [neg_one_mul, negative_logPoissonProfile]

end Singularity
