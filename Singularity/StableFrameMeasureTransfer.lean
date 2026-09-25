import Singularity.StableFrameSection
import Singularity.StableBoundaryProduct
import Singularity.LiouvilleFrameHaar

/-!
# Transfer of Haar-full stable properties to one-sided current lifts

A measurable property invariant along every lower horocycle holds almost
everywhere for a lifted current whenever it holds Haar-almost everywhere,
the current is absolutely continuous with respect to a backward-forward
product, and only the forward marginal is visually absolutely continuous.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure OnePoint Filter
open scoped MatrixGroups

namespace Singularity

attribute [local instance] slTwo_polishSpace slTwo_locallyCompactSpace
  frameStabilizer_measurableMul frameStabilizer_measurableInv
  frameFiberHaar_sigmaFinite frameFiberHaar_rightInvariant compactLiouvilleCurrent_sigmaFinite

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]

/-- One-sided visual absolute continuity transfers every measurable stable-saturated basin. -/
theorem ae_currentFrameLift_of_forward_ac
    (ρ : Measure SL(2, ℝ)) [IsHaarMeasure ρ]
    (α β : Measure (OnePoint ℝ)) [IsFiniteMeasure α] [IsFiniteMeasure β]
    [NullSingletonClass β] (J : Measure BoundaryPair) [SFinite J]
    (hJ : J ≪ boundaryPairMeasure α β) (hβ : β ≪ compactPoissonMeasure UpperHalfPlane.I)
    (P : SL(2, ℝ) → Prop) (hP : MeasurableSet {g | P g})
    (hsat : ∀ u g, P g → P (lowerShearMatrix u * g))
    (h : ∀ᵐ g ∂ρ, P g) : ∀ᵐ g ∂currentFrameLift J frameFiberHaar, P g := by
  let v := compactPoissonMeasure UpperHalfPlane.I
  let := compactPoissonMeasure_probability UpperHalfPlane.I
  let := compactPoissonMeasure_nullSingleton UpperHalfPlane.I
  have hL : ∀ᵐ g ∂currentFrameLift compactLiouvilleCurrent frameFiberHaar, P g :=
    (liouvilleFrameMeasure_measureClass ρ).1.ae_le h
  rw [← currentFrameLift_stable_coordinates] at hL
  have hL' := ae_of_ae_map measurable_stableFrameFromCoordinates.aemeasurable hL
  have hv : boundaryPairMeasure v v ≪ compactLiouvilleCurrent :=
    (boundaryPairCurrent_measureClass v v liouvilleBoundaryKernel
      continuous_liouvilleBoundaryKernel.measurable liouvilleBoundaryKernel_pos).2
  have href : ∀ᵐ q ∂(boundaryPairMeasure v v).prod frameFiberHaar,
      P (stableFrameFromCoordinates q) := (hv.prod AbsolutelyContinuous.rfl).ae_le hL'
  have htgt : ∀ᵐ q ∂(boundaryPairMeasure α β).prod frameFiberHaar,
      P (stableFrameFromCoordinates q) := by
    apply ae_boundaryPair_product_of_fibre_saturation v α v β frameFiberHaar hβ
      (fun q => P (stableFrameFromCoordinates q)) (hP.preimage measurable_stableFrameFromCoordinates)
    · intro p q h₀ hpq hp
      obtain ⟨u, hu⟩ := stableFrameFromCoordinates_fibre p q h₀ hpq
      rw [hu]
      exact hsat u _ hp
    · exact href
  rw [← currentFrameLift_stable_coordinates]
  exact (ae_map_iff measurable_stableFrameFromCoordinates.aemeasurable hP).mpr
    ((hJ.prod AbsolutelyContinuous.rfl).ae_le htgt)

end Singularity
