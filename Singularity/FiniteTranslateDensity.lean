import Singularity.StationaryDensity

/-!
# Densities of finite mixtures of translated laws on a region

A restricted measure identity gives the corresponding almost-everywhere
identity for the original translated Radon–Nikodym densities on that region.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal
namespace Singularity

/-- Local finite-mixture identities pass to actual real translated densities. -/
theorem stationaryRealDensity_finite_mixture_on_set
    {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
    (ν : Measure B) [IsFiniteMeasure ν]
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)
    (A : Finset Γ) (c : A → ℝ) (hc : ∀ a, 0 ≤ c a) (x : Γ)
    {E : Set B} (hE : MeasurableSet E)
    (heq : (Measure.map (fun ξ : B => x • ξ) ν).restrict E =
      ∑ a : A, ENNReal.ofReal (c a) • (Measure.map (fun ξ : B => (a : Γ) • ξ) ν).restrict E) :
    ∀ᵐ ξ ∂ν, ξ ∈ E → stationaryRealDensity ν x ξ =
      ∑ a : A, c a * stationaryRealDensity ν (a : Γ) ξ := by
  let f : B → ℝ≥0∞ := fun ξ => ∑ a : A, ENNReal.ofReal (c a) * stationaryDensity ν (a : Γ) ξ
  have hf : Measurable f := Finset.measurable_sum _ (fun a _ =>
    measurable_const.mul (measurable_stationaryDensity ν (a : Γ)))
  have hmix : ν.withDensity f =
      ∑ a : A, ENNReal.ofReal (c a) • Measure.map (fun ξ : B => (a : Γ) • ξ) ν := by
    ext S hS
    rw [withDensity_apply _ hS]
    change (∫⁻ ξ in S, ∑ a : A, ENNReal.ofReal (c a) * stationaryDensity ν (a : Γ) ξ ∂ν) = _
    rw [lintegral_finsetSum Finset.univ
      (f := fun (a : A) (ξ : B) => ENNReal.ofReal (c a) * stationaryDensity ν (a : Γ) ξ)
      (fun a _ => measurable_const.mul (measurable_stationaryDensity ν (a : Γ))),
      Measure.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [lintegral_const_mul _ (measurable_stationaryDensity ν (a : Γ)),
      Measure.smul_apply, smul_eq_mul]
    congr 1
    exact Measure.setLIntegral_rnDeriv (hq a) S
  have he : (ν.restrict E).withDensity (stationaryDensity ν x) = (ν.restrict E).withDensity f := by
    rw [← restrict_withDensity hE, ← restrict_withDensity hE,
      (show ν.withDensity (stationaryDensity ν x) = Measure.map (fun ξ : B => x • ξ) ν from
        Measure.withDensity_rnDeriv_eq _ _ (hq x)), hmix, heq]
    ext S hS
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]
  have hd : stationaryDensity ν x =ᵐ[ν.restrict E] f :=
    (withDensity_eq_iff_of_sigmaFinite (measurable_stationaryDensity ν x).aemeasurable hf.aemeasurable).mp he
  have hd' : ∀ᵐ ξ ∂ν, ξ ∈ E → stationaryDensity ν x ξ = f ξ := (ae_restrict_iff' hE).mp hd
  have hfinite : ∀ᵐ ξ ∂ν, ∀ a : A, stationaryDensity ν (a : Γ) ξ ≠ ⊤ :=
    ae_all_iff.mpr (fun a => (Measure.rnDeriv_lt_top (Measure.map (fun ξ : B => (a : Γ) • ξ) ν) ν).mono
      (fun _ h => h.ne))
  filter_upwards [hd', hfinite] with ξ hξ hfin hξE
  change (stationaryDensity ν x ξ).toReal = _
  rw [hξ hξE]
  change (∑ a : A, ENNReal.ofReal (c a) * stationaryDensity ν (a : Γ) ξ).toReal = _
  rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc a)]
  rfl

end Singularity
