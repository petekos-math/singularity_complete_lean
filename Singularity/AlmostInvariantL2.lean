import Singularity.MarkovEnergy
import Singularity.ReflectedSupport
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Failure of the spectral gap produces almost invariant L² vectors

The energy criterion is homogeneous, so absence of a spectral gap supplies
unit vectors of arbitrarily small energy. Positive support weights imply small
individual support displacements, and semigroup generation propagates this to
every group element. `L2InvariantMean.lean` supplies the subsequent invariant-mean construction.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical Topology

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ]

omit [MeasurableSingletonClass Γ] in
/-- A lower energy bound on unit vectors is equivalent to its homogeneous form. -/
theorem markovEnergy_lower_bound_of_unit (s : Finset Γ) (μ : Γ → ℝ) (c : ℝ)
    (hunit : ∀ f : GroupL2 Γ, ‖f‖ = 1 → c ≤ markovEnergy s μ f) :
    ∀ f : GroupL2 Γ, c * ‖f‖ ^ 2 ≤ markovEnergy s μ f := by
  intro f
  by_cases hf : f = 0
  · simp [hf, markovEnergy]
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hv : ‖((‖f‖⁻¹ : ℝ) : ℂ) • f‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  have h := hunit (((‖f‖⁻¹ : ℝ) : ℂ) • f) hv
  rw [markovEnergy_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hn), inv_pow, ← div_eq_inv_mul] at h
  exact (le_div_iff₀ (sq_pos_of_pos hn)).mp h

/-- Without a spectral gap there are unit vectors with arbitrarily small energy. -/
theorem exists_low_energy_unit_of_no_gap [Countable Γ] (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : ¬spectralRadius ℂ (rightMarkov s μ) < 1) {c : ℝ} (hc : 0 < c) :
    ∃ f : GroupL2 Γ, ‖f‖ = 1 ∧ markovEnergy s μ f < c := by
  by_contra h
  push Not at h
  exact hgap (rightMarkov_spectral_gap_of_energy s μ hμ hmass hc
    (markovEnergy_lower_bound_of_unit s μ c h))

omit [MeasurableSingletonClass Γ] in
/-- Vanishing energy forces vanishing displacement under each positive-weight jump. -/
theorem tendsto_translation_of_energy (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (f : ℕ → GroupL2 Γ)
    (he : Tendsto (fun n => markovEnergy s μ (f n)) atTop (nhds 0))
    {g : Γ} (hg : g ∈ s) (hpos : 0 < μ g) :
    Tendsto (fun n => ‖rightTranslation g (f n) - f n‖) atTop (nhds 0) := by
  have hterm (n : ℕ) : ‖rightTranslation g (f n) - f n‖ ^ 2 ≤
      (μ g)⁻¹ * markovEnergy s μ (f n) := by
    apply (le_inv_mul_iff₀ hpos).mpr
    exact Finset.single_le_sum (f := fun h => μ h * ‖rightTranslation h (f n) - f n‖ ^ 2)
      (fun h hh => mul_nonneg (hμ h hh) (sq_nonneg _)) hg
  have hsq : Tendsto (fun n => ‖rightTranslation g (f n) - f n‖ ^ 2) atTop (nhds 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) hterm
    simpa using he.const_mul (μ g)⁻¹
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

omit [MeasurableSingletonClass Γ] in
/-- Almost invariance under a generating support propagates to its full semigroup. -/
theorem tendsto_translation_of_mem_closure (s : Finset Γ) (f : ℕ → GroupL2 Γ)
    (hs : ∀ g ∈ s, Tendsto (fun n => ‖rightTranslation g (f n) - f n‖) atTop (nhds 0))
    {g : Γ} (hg : g ∈ Submonoid.closure (s : Set Γ)) :
    Tendsto (fun n => ‖rightTranslation g (f n) - f n‖) atTop (nhds 0) := by
  induction hg using Submonoid.closure_induction_left with
  | one => simpa only [rightTranslation_one, sub_self, norm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  | mul_left a ha b _ ih =>
    have hb (n : ℕ) : ‖rightTranslation (a * b) (f n) - f n‖ ≤
        ‖rightTranslation b (f n) - f n‖ + ‖rightTranslation a (f n) - f n‖ := by
      rw [← rightTranslation_mul]
      have he : rightTranslation a (rightTranslation b (f n)) - f n =
          rightTranslation a (rightTranslation b (f n) - f n) + (rightTranslation a (f n) - f n) := by
        rw [map_sub]; abel
      rw [he]
      exact (norm_add_le _ _).trans_eq (by rw [rightTranslation_norm])
    apply squeeze_zero (fun _ => norm_nonneg _) hb
    simpa using ih.add (hs a ha)

/-- Failure of the spectral gap gives a single sequence of unit vectors almost invariant
under every group element. No laziness or symmetry is assumed. -/
theorem exists_almostInvariantL2_of_no_gap (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : ¬spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ f : ℕ → GroupL2 Γ, (∀ n, ‖f n‖ = 1) ∧
      ∀ g : Γ, Tendsto (fun n => ‖rightTranslation g (f n) - f n‖) atTop (nhds 0) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  have he (n : ℕ) : ∃ f : GroupL2 Γ, ‖f‖ = 1 ∧ markovEnergy s μ f < 1 / ((n : ℝ) + 1) :=
    exists_low_energy_unit_of_no_gap s μ hμ hmass hgap (by positivity)
  choose f hf he using he
  have ht : Tendsto (fun n => markovEnergy s μ (f n)) atTop (nhds 0) :=
    squeeze_zero (fun n => markovEnergy_nonneg s μ hμ (f n))
      (fun n => (he n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨f, hf, fun g => ?_⟩
  exact tendsto_translation_of_mem_closure s f
    (fun a ha => tendsto_translation_of_energy s μ hμ f ht ha (hpos a ha))
    (by rw [hgen]; trivial)

end Singularity
