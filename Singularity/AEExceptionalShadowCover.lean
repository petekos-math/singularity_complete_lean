import Singularity.AdjustableExceptionalCover
import Singularity.VanishingErrorReturnCover

/-!
# Exceptional-set coverage modulo null sets

Measurable Radon–Nikodym shadows need not have pointwise geometric behavior
on a null exceptional domain. Eventual containment of their complements
almost everywhere is enough: countability and quasi-invariance transfer the
null sets through the finite correction argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Singularity

/-- The adjustable exceptional-set cover only needs containment almost
everywhere at each sufficiently late time, rather than pointwise containment. -/
theorem finite_eventual_cover_of_ae_adjustable_shadows
    {Γ B I : Type*} [Group Γ] [Countable Γ] [MeasurableSpace B]
    [TopologicalSpace B] [CompactSpace B] [RegularSpace B]
    [MulAction Γ B] [MeasurableConstSMul Γ B] [ContinuousConstSMul Γ B]
    (ν : Measure B) (hq : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) ν ≪ ν)
    (T : I → ℕ → Set B) (Z : Set B) (hZ : IsClosed Z)
    (hescape : ∀ ξ : B, ∃ a : Γ, a⁻¹ • ξ ∉ Z)
    (hshrink : ∀ U : Set B, IsOpen U → Z ⊆ U → ∃ i : I,
      ∀ᶠ n in atTop, ∀ᵐ ξ ∂ν, ξ ∉ T i n → ξ ∈ U) :
    ∃ i : I, ∃ F : Finset Γ,
      ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∀ᶠ n in atTop, a⁻¹ • ξ ∈ T i n := by
  obtain ⟨U, hU, hZU, F, hF⟩ := finite_corrections_avoid_exceptional_neighborhood Z hZ hescape
  obtain ⟨i, hi⟩ := hshrink U hU hZU
  obtain ⟨N, hN⟩ := eventually_atTop.mp hi
  have hg : ∀ᵐ ξ ∂ν, ∀ n : ℕ, N ≤ n → ξ ∉ T i n → ξ ∈ U :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun hn => hN n hn))
  have htrans : ∀ᵐ ξ ∂ν, ∀ a : Γ, ∀ n : ℕ, N ≤ n →
      a⁻¹ • ξ ∉ T i n → a⁻¹ • ξ ∈ U := by
    apply ae_all_iff.mpr
    intro a
    exact (show Measure.QuasiMeasurePreserving (fun ξ : B => a⁻¹ • ξ) ν ν from
      ⟨measurable_const_smul a⁻¹, hq a⁻¹⟩).ae hg
  refine ⟨i, F, ?_⟩
  filter_upwards [htrans] with ξ hξ
  obtain ⟨a, ha, hnot⟩ := hF ξ
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  by_contra hbad
  exact hnot (hξ a n hn hbad)

end Singularity
