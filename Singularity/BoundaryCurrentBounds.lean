import Singularity.BoundaryCurrentDensity
import Singularity.CocompactVisualErgodicity

/-!
# Uniform marginal bounds from a positive continuous current

For probability marginals absolutely continuous to visual measure, scalar
equality of their positive continuous current with Liouville current forces
both densities to be bounded above and away from zero. These are implications
from an explicit current identity, not assertions that the actual Naïm kernel
has already been constructed.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical ENNReal UpperHalfPlane

namespace Singularity

/-- The second marginal of the distinct-pair product is the prescribed second probability. -/
theorem boundaryPairMeasure_second_marginal (α β : Measure (OnePoint ℝ))
    [IsProbabilityMeasure α] [SFinite β] [NullSingletonClass β] :
    Measure.map (fun p : BoundaryPair => p.val.2) (boundaryPairMeasure α β) = β := by
  change Measure.map (Prod.snd ∘ Subtype.val) _ = _
  rw [← Measure.map_map measurable_snd measurable_subtype_coe,
    boundaryPairMeasure_map_eq, Measure.map_snd_prod, measure_univ, one_smul]

/-- Equality with a positive reference current upgrades marginal absolute continuity to equivalence. -/
theorem boundaryPairCurrent_reference_absolutelyContinuous
    (α β m : Measure (OnePoint ℝ)) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    [IsProbabilityMeasure m] [NullSingletonClass m]
    (hβ : β ≪ m) (K L : BoundaryPair → ℝ)
    (hL : Measurable L) (hpL : ∀ p, 0 < L p)
    (c : ℝ≥0∞) (hc : 0 < c)
    (heq : boundaryPairCurrent α β K = c • boundaryPairCurrent m m L) :
    m ≪ α ∧ m ≪ β := by
  let : NullSingletonClass β := ⟨fun x => hβ (measure_singleton x)⟩
  have h0 : boundaryPairMeasure m m ≪ c • boundaryPairCurrent m m L :=
    (boundaryPairCurrent_measureClass m m L hL hpL).2.trans (Measure.absolutelyContinuous_smul hc.ne')
  rw [← heq] at h0
  have hpair := h0.trans (withDensity_absolutelyContinuous (boundaryPairMeasure α β) _)
  have h1 := hpair.map (measurable_fst.comp measurable_subtype_coe)
  have h2 := hpair.map (measurable_snd.comp measurable_subtype_coe)
  simp only [Function.comp_def] at h1 h2
  rw [boundaryPairMeasure_first_marginal, boundaryPairMeasure_first_marginal] at h1
  rw [boundaryPairMeasure_second_marginal, boundaryPairMeasure_second_marginal] at h2
  exact ⟨h1,h2⟩

/-- Positive continuous off-diagonal kernels and current equality give common two-sided marginal density bounds. -/
theorem boundaryPairCurrent_uniform_density_bounds
    (α β m : Measure (OnePoint ℝ)) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    [IsProbabilityMeasure m] [NullSingletonClass m]
    (hα : α ≪ m) (hβ : β ≪ m)
    (K L : BoundaryPair → ℝ) (hK : Continuous K) (hL : Continuous L)
    (hpK : ∀ p, 0 < K p) (hpL : ∀ p, 0 < L p)
    (c : ℝ≥0∞) (hc : 0 < c) (hct : c < ⊤)
    (heq : boundaryPairCurrent α β K = c • boundaryPairCurrent m m L) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᵐ x ∂m,
      (a ≤ (α.rnDeriv m x).toReal ∧ (α.rnDeriv m x).toReal ≤ b) ∧
      (a ≤ (β.rnDeriv m x).toReal ∧ (β.rnDeriv m x).toReal ≤ b) := by
  let H : OnePoint ℝ × OnePoint ℝ → ℝ := fun p =>
    c.toReal * extendBoundaryPairKernel L p / extendBoundaryPairKernel K p
  have hp : ∀ x y : OnePoint ℝ, x ≠ y → 0 < H (x,y) := by
    intro x y hxy
    change 0 < c.toReal * extendBoundaryPairKernel L (⟨(x,y),hxy⟩ : BoundaryPair).val /
      extendBoundaryPairKernel K (⟨(x,y),hxy⟩ : BoundaryPair).val
    rw [extendBoundaryPairKernel_apply, extendBoundaryPairKernel_apply]
    exact div_pos (mul_pos (ENNReal.toReal_pos hc.ne' hct.ne) (hpL _)) (hpK _)
  have hH : ContinuousOn H {p | p.1 ≠ p.2} := by
    apply (continuousOn_const.mul (continuousOn_extendBoundaryPairKernel L hL)).div
      (continuousOn_extendBoundaryPairKernel K hK)
    intro p hp
    rw [show p = (⟨p,hp⟩ : BoundaryPair).val from rfl, extendBoundaryPairKernel_apply]
    exact (hpK _).ne'
  have hβ' := (boundaryPairCurrent_reference_absolutelyContinuous α β m hβ K L
    hL.measurable hpL c hc heq).2
  have hg : ∀ᵐ y ∂m, 0 < (β.rnDeriv m y).toReal := by
    filter_upwards [Measure.rnDeriv_pos' hβ', Measure.rnDeriv_lt_top β m] with y hy ht
    exact ENNReal.toReal_pos hy.ne' ht.ne
  have hi := boundaryPairCurrent_rnDeriv_identity α β m hα hβ K L hK.measurable hL.measurable
    (fun p => (hpK p).le) (fun p => (hpL p).le) c heq
  have hdiag : ∀ᵐ p ∂m.prod m, p.1 ≠ p.2 := by
    rw [ae_iff]
    simpa only [not_not] using compactBoundary_product_diagonal_null m m
  apply compact_product_density_bounds m (fun x => (α.rnDeriv m x).toReal)
    (fun y => (β.rnDeriv m y).toReal) H hH hp hg
  filter_upwards [hi, hdiag] with p hi hp
  have hk : extendBoundaryPairKernel K p ≠ 0 := by
    rw [show p = (⟨p,hp⟩ : BoundaryPair).val from rfl, extendBoundaryPairKernel_apply]
    exact (hpK _).ne'
  exact (eq_div_iff hk).mpr hi

/-- Two-sided real density bounds give the corresponding order bounds on measures. -/
theorem real_rnDeriv_measure_bounds {X : Type*} [MeasurableSpace X]
    (α m : Measure X) [SigmaFinite α] [SigmaFinite m] (hac : α ≪ m)
    (a b : ℝ) (h : ∀ᵐ x ∂m, a ≤ (α.rnDeriv m x).toReal ∧ (α.rnDeriv m x).toReal ≤ b) :
    ENNReal.ofReal a • m ≤ α ∧ α ≤ ENNReal.ofReal b • m := by
  have h1 := withDensity_mono (μ := m) (h.mono (fun _ hx => ENNReal.ofReal_le_ofReal hx.1))
  have h2 := withDensity_mono (μ := m) (h.mono (fun _ hx => ENNReal.ofReal_le_ofReal hx.2))
  rw [withDensity_const, real_rnDeriv_withDensity α m hac] at h1
  rw [withDensity_const, real_rnDeriv_withDensity α m hac] at h2
  exact ⟨h1,h2⟩

end Singularity
