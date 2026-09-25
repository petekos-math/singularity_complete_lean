import Singularity.LatticeObstruction
import Singularity.TranslatedAnalysis

/-!
# The actual lattice analysis operator has nontrivial kernel

The hypotheses concern finitely many nonnegative densities of mass at most one
and exponential decay. Boundedness and nontrivial kernel of H are conclusions.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Singularity

/-- The inner-product formula for translation of an L² equivalence class. -/
theorem inner_realTranslation_toLp (a : ℝ) {k : ℝ → ℂ} (hk : MemLp k 2 volume)
    (f : RealLineL2) : inner ℂ (realTranslation a (hk.toLp k)) f =
      ∫ t, conj (k (t - a)) * f t := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hraw := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae hk.coeFn_toLp
  filter_upwards [realTranslation_apply_ae a (hk.toLp k), hraw] with t ht hr
  rw [ht, hr]
  simp [RCLike.inner_apply, mul_comm]

/-- The analysis operator constructed from the profiles has a nonzero kernel.
No independent kernel hypothesis is needed. -/
theorem translated_analysis_has_kernel {J : Type*} [Fintype J]
    {τ : ℝ} (hτ : 0 < τ) (k : J → ℝ → ℝ) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hk : ∀ j t, 0 ≤ k j t)
    (hint : ∀ j, Integrable (k j)) (hmass : ∀ j, ∫ t, k j t ≤ 1)
    (hdecay : ∀ j t, k j t ≤ C j * Real.exp (-|t|)) :
    ∃ φ : RealLineL2, φ ≠ 0 ∧
      (translatedDensityFamily hτ k C hC hk hint hmass hdecay).analysis φ = 0 := by
  let K := translatedDensityFamily hτ k C hC hk hint hmass hdecay
  have hmem : ∀ j, MemLp (fun t => (k j t : ℂ)) 2 volume := by
    intro j
    simpa [K, translatedDensityFamily] using K.row_memL2 (0, j)
  let kL2 : J → RealLineL2 := fun j => (hmem j).toLp (fun t => (k j t : ℂ))
  obtain ⟨φ, hφ, ho⟩ := exists_orthogonal_lattice_translates_fintype kL2 hτ
  refine ⟨φ, hφ, ?_⟩
  ext p
  rcases p with ⟨n, j⟩
  rw [translated_analysis_apply]
  have h := ho n j
  rw [inner_realTranslation_toLp] at h
  simpa using h

/-- An injective operator cannot factor through this lattice analysis operator. -/
theorem impossible_translated_analysis_factorization {J : Type*} [Fintype J]
    {τ : ℝ} (hτ : 0 < τ) (k : J → ℝ → ℝ) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hk : ∀ j t, 0 ≤ k j t)
    (hint : ∀ j, Integrable (k j)) (hmass : ∀ j, ∫ t, k j t ≤ 1)
    (hdecay : ∀ j t, k j t ≤ C j * Real.exp (-|t|))
    (T : RealLineL2 →L[ℂ] RealLineL2)
    (M : SequenceL2 (ℤ × J) →L[ℂ] SequenceL2 (ℤ × J))
    (L : SequenceL2 (ℤ × J) →L[ℂ] RealLineL2)
    (hT : Function.Injective T)
    (hfactor : T = L.comp (M.comp
      (translatedDensityFamily hτ k C hC hk hint hmass hdecay).analysis)) : False :=
  impossible_factorization T _ M L hfactor hT
    (translated_analysis_has_kernel hτ k C hC hk hint hmass hdecay)

end Singularity
