import Singularity.GeometricNaimCurrent
import Singularity.CurrentFrameLift
import Singularity.FrameFiberHaar
import Singularity.CurrentFrameLocalFiniteness

/-!
# The actual Naïm frame measure

The previously constructed invariant Naïm current now has an explicit
nonzero sigma-finite frame lift, invariant under every real geodesic-flow time
and under right multiplication by the lattice. No visual absolute continuity
of either hitting measure is needed. The lift is locally finite. Finiteness after descent to the compact quotient
is established separately.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

attribute [local instance] slTwo_polishSpace frameStabilizer_measurableMul
  frameStabilizer_measurableInv frameFiberHaar_sigmaFinite frameFiberHaar_leftInvariant
  frameFiberHaar_rightInvariant

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
  (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)

/-- The actual Naïm current lifted by Haar measure on the full frame fibre. -/
def geometricNaimFrameMeasure : Measure SL(2, ℝ) :=
  currentFrameLift (geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z) frameFiberHaar

theorem geometricNaimFrameMeasure_sigmaFinite :
    SigmaFinite (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z) := by
  let := geometricNaimCurrent_sigmaFinite Γ s μ hpos hmass hgen hgap horbit z
  exact currentFrameLift_sigmaFinite _ _

theorem geometricNaimFrameMeasure_ne_zero :
    geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z ≠ 0 := by
  let : NeZero frameFiberHaar := ⟨frameFiberHaar_ne_zero⟩
  exact currentFrameLift_ne_zero _ _ (geometricNaimCurrent_ne_zero Γ s μ hpos hmass hgen hgap horbit z)

/-- The frame measure is invariant under every time of the geodesic flow. -/
theorem geometricNaimFrameMeasure_dilation_invariant (t : ℝ) :
    MeasurePreserving (fun g : SL(2, ℝ) => dilationMatrix t * g)
      (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z)
      (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z) := by
  let := geometricNaimCurrent_sigmaFinite Γ s μ hpos hmass hgen hgap horbit z
  exact currentFrameLift_dilation_invariant _ _ t

/-- The actual lattice acts on the frame measure by right measure-preserving translations. -/
theorem geometricNaimFrameMeasure_right_invariant (g : Γ) :
    MeasurePreserving (fun x : SL(2, ℝ) => x * (g : SL(2, ℝ)))
      (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z)
      (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z) := by
  let := geometricNaimCurrent_sigmaFinite Γ s μ hpos hmass hgen hgap horbit z
  apply currentFrameLift_right_invariant
  refine ⟨(continuous_const_smul (g : SL(2, ℝ))⁻¹).measurable, ?_⟩
  have he : (fun p : BoundaryPair => (g : SL(2, ℝ))⁻¹ • p) = (fun p : BoundaryPair => g⁻¹ • p) := by
    funext p
    apply Subtype.ext
    rfl
  rw [he]
  exact geometricNaimCurrent_invariant Γ s μ hpos hmass hgen hgap horbit z g⁻¹

/-- Endpoint projection recovers the exact Naïm-current measure class. -/
theorem geometricNaimFrameMeasure_endpoint_measureClass :
    (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z).map inverseFrameEndpoints ≪
      geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z ∧
    geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z ≪
      (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z).map inverseFrameEndpoints := by
  let : NeZero frameFiberHaar := ⟨frameFiberHaar_ne_zero⟩
  exact currentFrameLift_endpoint_measureClass _ _

/-- The endpoint image is also equivalent to the actual backward-forward hitting product. -/
theorem geometricNaimFrameMeasure_hittingPair_measureClass :
    (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z).map inverseFrameEndpoints ≪
      geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z ∧
    geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z ≪
      (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z).map inverseFrameEndpoints := by
  have h := geometricNaimFrameMeasure_endpoint_measureClass Γ s μ hpos hmass hgen hgap horbit z
  have hJ := geometricNaimCurrent_measureClass Γ s μ hpos hmass hgen hgap horbit z
  exact ⟨h.1.trans hJ.1, hJ.2.trans h.2⟩

/-- The actual frame measure is locally finite, with no visual-density assumption. -/
theorem geometricNaimFrameMeasure_locallyFinite :
    IsLocallyFiniteMeasure (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z) := by
  let := geometricNaimCurrent_locallyFinite Γ s μ hpos hmass hgen hgap horbit z
  let := frameFiberHaar_locallyFinite
  exact currentFrameLift_locallyFinite _ _

/-- The right lattice action preserves the frame lift, as an action-invariance instance. -/
theorem geometricNaimFrameMeasure_latticeInvariant :
    SMulInvariantMeasure Γ.op SL(2, ℝ)
      (geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z) := by
  constructor
  intro γ A hA
  let g : Γ := ⟨MulOpposite.unop (γ : SL(2, ℝ)ᵐᵒᵖ), γ.property⟩
  exact (geometricNaimFrameMeasure_right_invariant Γ s μ hpos hmass hgen hgap horbit z g).measure_preimage
    hA.nullMeasurableSet

end Singularity
