import Singularity.LiouvilleCurrent
import Singularity.CompactProductDensity

/-!
# Recovering the product of boundary densities from current equality

The Radon–Nikodym densities here belong to the actual input measures. Equality
of the off-diagonal currents yields their scalar product identity almost
everywhere on the whole boundary square, with the null diagonal removed.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical ENNReal

namespace Singularity

/-- Real Radon–Nikodym derivatives reconstruct an absolutely continuous finite measure. -/
theorem real_rnDeriv_withDensity {X : Type*} [MeasurableSpace X]
    (α m : Measure X) [SigmaFinite α] [SigmaFinite m] (hac : α ≪ m) :
    m.withDensity (fun x => ENNReal.ofReal ((α.rnDeriv m x).toReal)) = α := by
  calc
    _ = m.withDensity (α.rnDeriv m) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top α m] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    _ = α := Measure.withDensity_rnDeriv_eq α m hac

/-- The zero extension of a nonnegative kernel is nonnegative. -/
theorem extendBoundaryPairKernel_nonneg (K : BoundaryPair → ℝ) (hp : ∀ p, 0 ≤ K p)
    (p : OnePoint ℝ × OnePoint ℝ) : 0 ≤ extendBoundaryPairKernel K p := by
  by_cases h : p.1 = p.2
  · rcases p with ⟨x,y⟩
    simp only at h
    rw [h, extendBoundaryPairKernel_diagonal]
  · exact (extendBoundaryPairKernel_apply K ⟨p,h⟩).symm ▸ hp ⟨p,h⟩

/-- The zero extension retains continuity on the off-diagonal open set. -/
theorem continuousOn_extendBoundaryPairKernel (K : BoundaryPair → ℝ) (hK : Continuous K) :
    ContinuousOn (extendBoundaryPairKernel K) {p | p.1 ≠ p.2} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun p : BoundaryPair => extendBoundaryPairKernel K p.val)
  have he : (fun p : BoundaryPair => extendBoundaryPairKernel K p.val) = K :=
    funext (extendBoundaryPairKernel_apply K)
  rw [he]
  exact hK

/-- Equality of currents determines the product of the actual Radon–Nikodym densities. -/
theorem boundaryPairCurrent_rnDeriv_identity
    (α β m : Measure (OnePoint ℝ)) [IsFiniteMeasure α] [IsFiniteMeasure β]
    [IsProbabilityMeasure m] [NullSingletonClass m]
    (hα : α ≪ m) (hβ : β ≪ m)
    (K L : BoundaryPair → ℝ) (hK : Measurable K) (hL : Measurable L)
    (hpK : ∀ p, 0 ≤ K p) (hpL : ∀ p, 0 ≤ L p)
    (c : ℝ≥0∞)
    (heq : boundaryPairCurrent α β K = c • boundaryPairCurrent m m L) :
    ∀ᵐ p ∂m.prod m,
      (α.rnDeriv m p.1).toReal * (β.rnDeriv m p.2).toReal * extendBoundaryPairKernel K p =
        c.toReal * extendBoundaryPairKernel L p := by
  let : NullSingletonClass β := ⟨fun x => hβ (measure_singleton x)⟩
  have hmap := congrArg (Measure.map (Subtype.val : BoundaryPair → OnePoint ℝ × OnePoint ℝ)) heq
  rw [Measure.map_smul c measurable_subtype_coe.aemeasurable, boundaryPairCurrent_map α β K hK, boundaryPairCurrent_map m m L hL] at hmap
  have hα' := real_rnDeriv_withDensity α m hα
  have hβ' := real_rnDeriv_withDensity β m hβ
  rw [← hα', ← hβ', weightedProduct_real_density] at hmap
  · exact real_density_eq_of_measure_eq_smul _ _ _
      (((Measure.measurable_rnDeriv α m).ennreal_toReal.comp measurable_fst).mul
        ((Measure.measurable_rnDeriv β m).ennreal_toReal.comp measurable_snd) |>.mul
        (measurable_extendBoundaryPairKernel K hK))
      (measurable_extendBoundaryPairKernel L hL)
      (Eventually.of_forall (fun p => mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        (extendBoundaryPairKernel_nonneg K hpK p)))
      (Eventually.of_forall (extendBoundaryPairKernel_nonneg L hpL)) c hmap
  · exact (Measure.measurable_rnDeriv α m).ennreal_toReal
  · exact (Measure.measurable_rnDeriv β m).ennreal_toReal
  · exact measurable_extendBoundaryPairKernel K hK
  · exact fun _ => ENNReal.toReal_nonneg
  · exact fun _ => ENNReal.toReal_nonneg

end Singularity
