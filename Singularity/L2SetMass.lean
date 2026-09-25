import Singularity.GreenBoundary
import Singularity.MarkovAdjoint
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Probability masses associated with unit L² vectors

The squared L² mass on a subset is nonnegative and finitely additive, and a
unit vector has total mass one. Restriction is a contraction, so the mass changes
by at most (‖f‖+‖g‖)‖f-g‖. This supplies the invariant-mean construction from
almost invariant vectors without a separate coarea argument.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical

namespace Singularity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

/-- Squared L² mass of a subset. -/
def l2SetMass (f : GroupL2 X) (A : Set X) : ℝ :=
  ∫ x in A, ‖f x‖ ^ 2 ∂Measure.count

omit [MeasurableSingletonClass X] [Countable X] in
theorem l2SetMass_nonneg (f : GroupL2 X) (A : Set X) : 0 ≤ l2SetMass f A :=
  integral_nonneg (fun _ => sq_nonneg _)

omit [MeasurableSingletonClass X] [Countable X] in
theorem l2SetMass_empty (f : GroupL2 X) : l2SetMass f ∅ = 0 := by simp [l2SetMass]

/-- The mass equals the squared norm of the actual supported restriction. -/
theorem l2SetMass_eq_restriction (f : GroupL2 X) (A : Set X) :
    l2SetMass f A = ‖supportedRestriction A f‖ ^ 2 := by
  let r : GroupL2 X := (supportedRestriction A f : GroupL2 X)
  have hn : ‖r‖ ^ 2 = ∫ x, ‖r x‖ ^ 2 ∂Measure.count := by
    simpa only [Lp.toLp_coeFn] using toL2_norm_sq (Lp.memLp r)
  have he (x : X) : ‖r x‖ ^ 2 = A.indicator (fun x => ‖f x‖ ^ 2) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      rw [show r x = f x from supportedRestriction_apply A f ⟨x, hx⟩]
    · rw [indicator_of_notMem hx]
      have hr : r x = 0 := (supportedRestriction A f).property x hx
      rw [hr, norm_zero, zero_pow (by norm_num)]
  change l2SetMass f A = ‖r‖ ^ 2
  rw [hn]
  simp_rw [he]
  exact (integral_indicator (Set.to_countable A).measurableSet).symm

/-- Restriction bounds the mass by the squared norm of the whole vector. -/
theorem l2SetMass_le_norm_sq (f : GroupL2 X) (A : Set X) : l2SetMass f A ≤ ‖f‖ ^ 2 := by
  rw [l2SetMass_eq_restriction]
  exact pow_le_pow_left₀ (norm_nonneg _) (supportedRestriction_norm_le A f) 2

omit [MeasurableSingletonClass X] [Countable X] in
/-- Total squared mass is the squared Hilbert norm. -/
theorem l2SetMass_univ (f : GroupL2 X) : l2SetMass f univ = ‖f‖ ^ 2 := by
  rw [l2SetMass, setIntegral_univ]
  symm
  simpa only [Lp.toLp_coeFn] using toL2_norm_sq (Lp.memLp f)

/-- Disjoint sets have additive squared mass. -/
theorem l2SetMass_union (f : GroupL2 X) (A B : Set X) (hAB : Disjoint A B) :
    l2SetMass f (A ∪ B) = l2SetMass f A + l2SetMass f B := by
  exact setIntegral_union hAB (Set.to_countable B).measurableSet
    ((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num)).integrableOn
    ((Lp.memLp f).integrable_norm_pow (p := 2) (by norm_num)).integrableOn

/-- Squared set masses are uniformly continuous on bounded subsets of L². -/
theorem l2SetMass_sub_le (f g : GroupL2 X) (A : Set X) :
    |l2SetMass f A - l2SetMass g A| ≤ (‖f‖ + ‖g‖) * ‖f - g‖ := by
  rw [l2SetMass_eq_restriction, l2SetMass_eq_restriction]
  have hd : |‖supportedRestriction A f‖ - ‖supportedRestriction A g‖| ≤ ‖f - g‖ := by
    apply (abs_norm_sub_norm_le _ _).trans
    rw [← map_sub]
    exact supportedRestriction_norm_le A (f - g)
  have he : ‖supportedRestriction A f‖ ^ 2 - ‖supportedRestriction A g‖ ^ 2 =
      (‖supportedRestriction A f‖ - ‖supportedRestriction A g‖) *
        (‖supportedRestriction A f‖ + ‖supportedRestriction A g‖) := by ring
  rw [he, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have h := mul_le_mul hd (add_le_add (supportedRestriction_norm_le A f) (supportedRestriction_norm_le A g))
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg (f - g))
  simpa only [mul_comm] using h

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ] [Countable Γ]

omit [MeasurableSingletonClass Γ] [Countable Γ] in
/-- Right translation of an L² vector translates its set mass in the opposite coordinate. -/
theorem l2SetMass_rightTranslation (g : Γ) (f : GroupL2 Γ) (A : Set Γ) :
    l2SetMass (rightTranslation g f) A = l2SetMass f ((fun x => x * g) '' A) := by
  unfold l2SetMass
  rw [(measurePreserving_mul_right Measure.count g).setIntegral_image_emb
    (MeasurableEquiv.mulRight g).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Measure.ae_count_iff.mp (rightTranslation_apply_ae g f) x]

end Singularity
