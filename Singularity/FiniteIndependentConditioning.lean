import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Conditioning a finite variable against an independent future

This formula will identify the conditional boundary probabilities of a random
walk: condition on its finite prefix and integrate over the independent tail.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace Singularity

/-- Given a finite-valued observed variable and an independent variable,
conditional expectation averages only over the independent variable. -/
theorem condExp_finite_independent {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [Fintype A] [MeasurableSingletonClass A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y P) (f : A → B → ℝ)
    (hf : ∀ a, Measurable (f a)) (hint : ∀ a, Integrable (fun ω => f a (Y ω)) P) :
    P[fun ω => f (X ω) (Y ω) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun ω => ∫ η, f (X ω) (Y η) ∂P := by
  let m := MeasurableSpace.comap X inferInstance
  have hXm : @Measurable Ω A m _ X := Measurable.of_comap_le le_rfl
  have hparts (a : A) :
      P[(X ⁻¹' {a}).indicator (fun ω => f a (Y ω)) | m] =ᵐ[P]
        (X ⁻¹' {a}).indicator (fun _ => ∫ η, f a (Y η) ∂P) := by
    have hi := condExp_indep_eq hY.comap_le hX.comap_le
      (((hf a).comp (Measurable.of_comap_le (le_rfl :
        MeasurableSpace.comap Y inferInstance ≤ MeasurableSpace.comap Y inferInstance))).stronglyMeasurable)
      hind.symm
    exact (condExp_indicator (hint a) (hXm (measurableSet_singleton a))).trans
      hi.indicator
  have he : (fun ω => f (X ω) (Y ω)) =
      ∑ a : A, (X ⁻¹' {a}).indicator (fun ω => f a (Y ω)) := by
    funext ω
    simp [Set.indicator, eq_comm]
  rw [he]
  have hs := condExp_finsetSum
    (fun a (_ : a ∈ (Finset.univ : Finset A)) =>
      (hint a).indicator (hX (measurableSet_singleton a))) m
  filter_upwards [hs, ae_all_iff.mpr hparts] with ω hω hp
  change _ = _ at hω
  rw [hω]
  simp only [Finset.sum_apply]
  simp_rw [hp]
  simp [Set.indicator, eq_comm]

end Singularity
