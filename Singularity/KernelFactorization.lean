import Singularity.DensityVector
import Singularity.LiouvilleOperator

/-!
# From a scalar kernel identity to an operator factorization

On L¹∩L², density analysis is a Bochner integral. Pairing these integrals
identifies the kernel of H₋* M H₊. Schwartz density then extends the identity
to all of L². The scalar kernel identity is an explicit hypothesis; its
geometric and probabilistic derivation is not formalized here.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Singularity

/-- Integration commutes with the conjugate-linear argument of the inner product. -/
theorem integral_inner_first {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] {u : ℝ → E}
    (hu : Integrable u) (y : E) :
    (∫ s, inner ℂ (u s) y) = inner ℂ (∫ s, u s) y := by
  have h := congrArg (conj : ℂ → ℂ) (integral_inner (𝕜 := ℂ) hu y)
  rw [← integral_conj] at h
  simpa only [inner_conj_symm] using h

/-- Two Bochner integrals may be paired through a bounded operator. -/
theorem inner_integral_operator_integral {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (M : F →L[ℂ] E) {u : ℝ → E} {v : ℝ → F}
    (hu : Integrable u) (hv : Integrable v) :
    inner ℂ (∫ s, u s) (M (∫ t, v t)) =
      ∫ s, ∫ t, inner ℂ (u s) (M (v t)) := by
  rw [← integral_inner_first hu]
  congr 1
  funext s
  rw [← M.integral_comp_comm hv, integral_inner (M.integrable_comp hv)]

/-- The corresponding double integral is absolutely integrable. -/
theorem integrable_inner_operator_prod {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (M : F →L[ℂ] E) {u : ℝ → E} {v : ℝ → F}
    (hu : Integrable u) (hv : Integrable v) :
    Integrable (fun p : ℝ × ℝ => inner ℂ (u p.1) (M (v p.2))) (volume.prod volume) := by
  apply ((hu.norm.mul_prod hv.norm).const_mul ‖M‖).mono'
    (hu.aestronglyMeasurable.comp_fst.inner
      (M.continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable.comp_snd))
  exact Filter.Eventually.of_forall (fun p => by
    calc
      ‖inner ℂ (u p.1) (M (v p.2))‖ ≤ ‖u p.1‖ * ‖M (v p.2)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u p.1‖ * (‖M‖ * ‖v p.2‖) :=
        mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)
      _ = ‖M‖ * (‖u p.1‖ * ‖v p.2‖) := by ring)

variable {ι : Type*} [Countable ι]

/-- The scalar kernel obtained from the two actual density columns. -/
def densityPairingKernel (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) (s t : ℝ) : ℂ :=
  inner ℂ (Kminus.column s) (M (Kplus.column t))

/-- The bounded operator represented by this kernel. -/
def densityFactorization (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) : RealLineL2 →L[ℂ] RealLineL2 :=
  Kminus.analysis.adjoint.comp (M.comp Kplus.analysis)

/-- Exact weak kernel formula on L¹∩L². -/
theorem densityFactorization_inner (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) (f h : RealLineL2)
    (hf : Integrable (f : ℝ → ℂ)) (hh : Integrable (h : ℝ → ℂ)) :
    inner ℂ h (densityFactorization Kminus Kplus M f) =
      ∫ s, ∫ t, densityPairingKernel Kminus Kplus M s t * inner ℂ (h s) (f t) := by
  change inner ℂ h (Kminus.analysis.adjoint (M (Kplus.analysis f))) = _
  rw [Kminus.analysis.adjoint_inner_right, Kminus.analysis_eq_integral h hh,
    Kplus.analysis_eq_integral f hf,
    inner_integral_operator_integral M (Kminus.column_integrable hh) (Kplus.column_integrable hf)]
  congr 1
  funext s
  congr 1
  funext t
  simp only [map_smul, inner_smul_left, inner_smul_right, densityPairingKernel,
    RCLike.inner_apply]
  ring

/-- Absolute integrability of the physical pairing kernel on L¹∩L². -/
theorem densityPairingKernel_integrable (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) {f h : ℝ → ℂ}
    (hf : Integrable f) (hh : Integrable h) :
    Integrable (fun p : ℝ × ℝ => densityPairingKernel Kminus Kplus M p.1 p.2 *
      inner ℂ (h p.1) (f p.2)) (volume.prod volume) := by
  apply (integrable_inner_operator_prod M (Kminus.column_integrable hh)
    (Kplus.column_integrable hf)).congr
  exact Filter.Eventually.of_forall (fun p => by
    simp only [map_smul, inner_smul_left, inner_smul_right, densityPairingKernel,
      RCLike.inner_apply]
    ring)

/-- Weak agreement on Schwartz tests determines a bounded L² operator. -/
theorem operator_eq_of_schwartz_pairings (C D : RealLineL2 →L[ℂ] RealLineL2)
    (hpair : ∀ f h : SchwartzMap ℝ ℂ,
      inner ℂ (h.toLp 2) (C (f.toLp 2)) = inner ℂ (h.toLp 2) (D (f.toLp 2))) : C = D := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume) ENNReal.ofNat_ne_top
  have he (f : SchwartzMap ℝ ℂ) : C (f.toLp 2) = D (f.toLp 2) := by
    apply ext_inner_left ℂ
    have hall : (fun x : RealLineL2 => inner ℂ x (C (f.toLp 2))) =
        (fun x : RealLineL2 => inner ℂ x (D (f.toLp 2))) :=
      hd.equalizer (continuous_id.inner continuous_const)
        (continuous_id.inner continuous_const) (funext (fun h => hpair f h))
    exact congrFun hall
  have hall := hd.equalizer C.continuous D.continuous (funext he)
  exact DFunLike.coe_injective hall

/-- An a.e. scalar kernel identity implies the genuine bounded-operator identity. -/
theorem liouville_factorization_of_kernel_identity
    (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) (c : ℝ)
    (hkernel : ∀ᵐ s, ∀ᵐ t, densityPairingKernel Kminus Kplus M s t =
      ((c / (4 * Real.cosh ((s - t) / 2) ^ 2) : ℝ) : ℂ)) :
    liouvilleConvolution c = densityFactorization Kminus Kplus M := by
  apply operator_eq_of_schwartz_pairings
  intro f h
  have hf : Integrable (f.toLp 2 : ℝ → ℂ) :=
    f.integrable.congr (f.coeFn_toLp 2 volume).symm
  have hh : Integrable (h.toLp 2 : ℝ → ℂ) :=
    h.integrable.congr (h.coeFn_toLp 2 volume).symm
  rw [liouvilleConvolution_inner_cosh, densityFactorization_inner Kminus Kplus M _ _ hf hh]
  apply integral_congr_ae
  filter_upwards [hkernel] with s hs
  apply integral_congr_ae
  filter_upwards [hs] with t ht
  rw [ht]

/-- The product-a.e. formulation supplied by an equality of current densities. -/
theorem liouville_factorization_of_kernel_identity_prod
    (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) (c : ℝ)
    (hkernel : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      densityPairingKernel Kminus Kplus M p.1 p.2 =
        ((c / (4 * Real.cosh ((p.1 - p.2) / 2) ^ 2) : ℝ) : ℂ)) :
    liouvilleConvolution c = densityFactorization Kminus Kplus M :=
  liouville_factorization_of_kernel_identity Kminus Kplus M c
    (Measure.ae_ae_of_ae_prod hkernel)

/-- The analytic contradiction now requires only the scalar boundary-kernel
identity, not an assumed factorization of bounded operators. -/
theorem impossible_liouville_kernel_identity {J : Type*} [Fintype J]
    {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) (k : J → ℝ → ℝ) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hk : ∀ j t, 0 ≤ k j t)
    (hint : ∀ j, Integrable (k j)) (hmass : ∀ j, ∫ t, k j t ≤ 1)
    (hdecay : ∀ j t, k j t ≤ C j * Real.exp (-|t|))
    (Kminus : DensityFamily ℝ (ℤ × J) volume)
    (M : SequenceL2 (ℤ × J) →L[ℂ] SequenceL2 (ℤ × J))
    (hkernel : ∀ᵐ s, ∀ᵐ t, densityPairingKernel Kminus
      (translatedDensityFamily hτ k C hC hk hint hmass hdecay) M s t =
        ((c / (4 * Real.cosh ((s - t) / 2) ^ 2) : ℝ) : ℂ)) : False := by
  exact impossible_liouville_factorization hτ hc k C hC hk hint hmass hdecay M
    Kminus.analysis.adjoint (liouville_factorization_of_kernel_identity Kminus
      (translatedDensityFamily hτ k C hC hk hint hmass hdecay) M c hkernel)

end Singularity
