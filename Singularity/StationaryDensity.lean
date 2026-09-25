import Singularity.StationaryQuasiInvariant
import Singularity.ReflectedSupport
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Radon–Nikodym densities of stationary boundary translates

The densities here are derivatives of actual pushforward measures, not assumed
Martin kernels. Semigroup generation proves positivity; stationarity proves
their harmonic equation. Identification with geometric Martin limits remains
a separate obligation.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical

namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
    [MeasurableConstSMul Γ B]

/-- The extended Radon–Nikodym density of the law viewed from a group element. -/
def stationaryDensity (ν : Measure B) (g : Γ) : B → ℝ≥0∞ :=
  (Measure.map (fun ξ : B => g • ξ) ν).rnDeriv ν

omit [MeasurableConstSMul Γ B] in
theorem measurable_stationaryDensity (ν : Measure B) (g : Γ) :
    Measurable (stationaryDensity ν g) := Measure.measurable_rnDeriv _ _

/-- Translating stationarity gives the harmonic equation for the family of laws. -/
theorem stationary_translate_harmonic (s : Finset Γ) (μ : Γ → ℝ) (ν : Measure B)
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν)
    (x : Γ) : Measure.map (fun ξ : B => x • ξ) ν =
      ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (x * g) • ξ) ν := by
  nth_rw 1 [hstat]
  rw [Measure.map_finset_sum (measurable_const_smul x).aemeasurable]
  apply Finset.sum_congr rfl
  intro g _
  rw [Measure.map_smul _ (measurable_const_smul x).aemeasurable,
    Measure.map_map (measurable_const_smul x) (measurable_const_smul (g : Γ))]
  congr 2
  funext ξ
  exact (mul_smul x (g : Γ) ξ).symm

variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (ν : Measure B) [IsFiniteMeasure ν]
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν)

include hpos hgen hstat in
/-- The stationary density reconstructs the actual translated law. -/
theorem stationaryDensity_withDensity (g : Γ) :
    ν.withDensity (stationaryDensity ν g) = Measure.map (fun ξ : B => g • ξ) ν :=
  Measure.withDensity_rnDeriv_eq _ _ (stationary_translate_equivalent s μ hpos hgen ν hstat g).1

include hpos hgen hstat in
/-- Each translate has a positive finite density almost everywhere. -/
theorem stationaryDensity_positive_finite (g : Γ) :
    ∀ᵐ ξ ∂ν, 0 < stationaryDensity ν g ξ ∧ stationaryDensity ν g ξ < ∞ := by
  exact (Measure.rnDeriv_pos' (stationary_translate_equivalent s μ hpos hgen ν hstat g).2).and
    (Measure.rnDeriv_lt_top _ _)

omit [MeasurableConstSMul Γ B] in
/-- The density is normalized at the identity. -/
theorem stationaryDensity_one : stationaryDensity ν (1 : Γ) =ᵐ[ν] fun _ => 1 := by
  unfold stationaryDensity
  have he : (fun ξ : B => (1 : Γ) • ξ) = id := by funext ξ; exact one_smul Γ ξ
  rw [he, Measure.map_id]
  exact Measure.rnDeriv_self ν

include hpos hgen hstat in
/-- The actual Radon–Nikodym derivatives satisfy the right-walk harmonic equation. -/
theorem stationaryDensity_harmonic (x : Γ) :
    stationaryDensity ν x =ᵐ[ν]
      fun ξ => ∑ g : s, ENNReal.ofReal (μ g) * stationaryDensity ν (x * g) ξ := by
  have hm : Measurable (fun ξ => ∑ g : s,
      ENNReal.ofReal (μ g) * stationaryDensity ν (x * g) ξ) := by
    exact Finset.measurable_sum Finset.univ (fun (g : s) _ =>
      (show Measurable (fun _ : B => ENNReal.ofReal (μ g)) from measurable_const).mul
        (measurable_stationaryDensity ν (x * g)))
  apply (withDensity_eq_iff_of_sigmaFinite
    (measurable_stationaryDensity ν x).aemeasurable hm.aemeasurable).mp
  rw [stationaryDensity_withDensity s μ hpos hgen ν hstat,
    stationary_translate_harmonic s μ ν hstat x]
  symm
  ext t ht
  rw [withDensity_apply _ ht, lintegral_finsetSum Finset.univ
    (f := fun (g : s) (ξ : B) => ENNReal.ofReal (μ g) * stationaryDensity ν (x * g) ξ)
    (fun (g : s) _ =>
    (show Measurable (fun _ : B => ENNReal.ofReal (μ g)) from measurable_const).mul
      (measurable_stationaryDensity ν (x * g))), Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro g _
  rw [lintegral_const_mul _ (measurable_stationaryDensity ν (x * g)),
    ← withDensity_apply _ ht, stationaryDensity_withDensity s μ hpos hgen ν hstat,
    Measure.smul_apply, smul_eq_mul]

include hpos hgen hstat in
/-- For a countable group all normalization, positivity and harmonic identities hold together. -/
theorem stationaryDensity_ae_harmonic :
    ∀ᵐ ξ ∂ν, stationaryDensity ν (1 : Γ) ξ = 1 ∧
      ∀ x : Γ, (0 < stationaryDensity ν x ξ ∧ stationaryDensity ν x ξ < ∞) ∧
        stationaryDensity ν x ξ = ∑ g : s,
          ENNReal.ofReal (μ g) * stationaryDensity ν (x * g) ξ := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hp := ae_all_iff.mpr (stationaryDensity_positive_finite s μ hpos hgen ν hstat)
  have hh := ae_all_iff.mpr (stationaryDensity_harmonic s μ hpos hgen ν hstat)
  filter_upwards [stationaryDensity_one (Γ := Γ) ν, hp, hh] with ξ hn hp hh
  exact ⟨hn, fun x => ⟨hp x, hh x⟩⟩

/-- The real-valued derivative used by the harmonic-function and Martin modules. -/
def stationaryRealDensity (ν : Measure B) (g : Γ) (ξ : B) : ℝ :=
  (stationaryDensity ν g ξ).toReal

include hpos hgen hstat in
/-- Real Radon–Nikodym derivatives form positive normalized harmonic functions almost everywhere. -/
theorem stationaryRealDensity_ae_harmonic :
    ∀ᵐ ξ ∂ν, stationaryRealDensity ν (1 : Γ) ξ = 1 ∧
      ∀ x : Γ, 0 < stationaryRealDensity ν x ξ ∧
        stationaryRealDensity ν x ξ = ∑ g : s, μ g * stationaryRealDensity ν (x * g) ξ := by
  filter_upwards [stationaryDensity_ae_harmonic s μ hpos hgen ν hstat] with ξ hξ
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  · simp only [stationaryRealDensity, hξ.1, ENNReal.toReal_one]
  · exact ENNReal.toReal_pos (hξ.2 x).1.1.ne' (hξ.2 x).1.2.ne
  · have he := congrArg ENNReal.toReal (hξ.2 x).2
    rw [ENNReal.toReal_sum (fun (g : s) _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hξ.2 (x * g)).1.2.ne)] at he
    change (stationaryDensity ν x ξ).toReal = _
    rw [he]
    apply Finset.sum_congr rfl
    intro g _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hpos g g.property).le]
    rfl

include hpos hgen hstat in
/-- Derivatives of actual translates satisfy the Radon–Nikodym cocycle identity. -/
theorem stationaryDensity_cocycle (g h : Γ) :
    ∀ᵐ ξ ∂ν, stationaryDensity ν (g * h) ξ =
      stationaryDensity ν g ξ * stationaryDensity ν h (g⁻¹ • ξ) := by
  have hcomp : Measure.map (fun ξ : B => g • ξ) (Measure.map (fun ξ : B => h • ξ) ν) =
      Measure.map (fun ξ : B => (g * h) • ξ) ν := by
    rw [Measure.map_map (measurable_const_smul g) (measurable_const_smul h)]
    congr 1
    funext ξ
    exact (mul_smul g h ξ).symm
  have hm := (measurableEmbedding_const_smul (α := B) g).rnDeriv_map
    (Measure.map (fun ξ : B => h • ξ) ν) ν
  rw [hcomp] at hm
  have hq : Measure.QuasiMeasurePreserving (fun ξ : B => g⁻¹ • ξ) ν ν :=
    ⟨measurable_const_smul g⁻¹, (stationary_translate_equivalent s μ hpos hgen ν hstat g⁻¹).1⟩
  have hac : Measure.map (fun ξ : B => (g * h) • ξ) ν ≪
      Measure.map (fun ξ : B => g • ξ) ν := by
    rw [← hcomp]
    exact ((stationary_translate_equivalent s μ hpos hgen ν hstat h).1).map
      (measurable_const_smul g)
  have hc := Measure.rnDeriv_mul_rnDeriv (κ := ν) hac
  filter_upwards [hq.ae hm, hc] with ξ hm hc
  simp only [smul_inv_smul] at hm
  change _ * stationaryDensity ν g ξ = stationaryDensity ν (g * h) ξ at hc
  rw [hm] at hc
  exact hc.symm.trans (mul_comm _ _)

end Singularity
