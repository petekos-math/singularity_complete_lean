import Singularity.BoundaryPairs
import Singularity.StationaryCurrent

/-!
# Invariance on the actual off-diagonal boundary space

Extending a kernel by zero on the diagonal connects its pair-space measure to
the weighted boundary product. The diagonal has zero product mass. Covariance
in the actual Radon--Nikodym derivatives therefore proves invariance directly
on ordered distinct endpoints. The covariance hypothesis remains explicit.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups ENNReal

namespace Singularity

/-- The pair-space inclusion is a measurable embedding. -/
theorem measurableEmbedding_boundaryPair :
    MeasurableEmbedding (Subtype.val : BoundaryPair → OnePoint ℝ × OnePoint ℝ) :=
  MeasurableEmbedding.subtype_coe isOpen_boundaryPair.measurableSet

/-- Extend an off-diagonal kernel by zero to the compact boundary square. -/
def extendBoundaryPairKernel (K : BoundaryPair → ℝ) : OnePoint ℝ × OnePoint ℝ → ℝ :=
  Function.extend Subtype.val K (fun _ => 0)

theorem extendBoundaryPairKernel_apply (K : BoundaryPair → ℝ) (p : BoundaryPair) :
    extendBoundaryPairKernel K p.val = K p :=
  Subtype.val_injective.extend_apply _ _ _

/-- The extension contributes no artificial diagonal mass. -/
theorem extendBoundaryPairKernel_diagonal (K : BoundaryPair → ℝ) (x : OnePoint ℝ) :
    extendBoundaryPairKernel K (x, x) = 0 := by
  unfold extendBoundaryPairKernel
  apply Function.extend_apply'
  rintro ⟨p, hp⟩
  apply p.property
  rw [hp]

theorem measurable_extendBoundaryPairKernel (K : BoundaryPair → ℝ) (hK : Measurable K) :
    Measurable (extendBoundaryPairKernel K) :=
  measurableEmbedding_boundaryPair.measurable_extend hK measurable_const

/-- Embedding the current into the square gives the full weighted product. -/
theorem boundaryPairCurrent_map (μ ν : Measure (OnePoint ℝ)) [SFinite ν] [NullSingletonClass ν]
    (K : BoundaryPair → ℝ) (hK : Measurable K) :
    Measure.map Subtype.val (boundaryPairCurrent μ ν K) =
      (μ.prod ν).withDensity (fun p => ENNReal.ofReal (extendBoundaryPairKernel K p)) := by
  have h := map_withDensity_comp (Subtype.val : BoundaryPair → OnePoint ℝ × OnePoint ℝ)
    measurable_subtype_coe (boundaryPairMeasure μ ν)
    (fun p => ENNReal.ofReal (extendBoundaryPairKernel K p))
    (measurable_extendBoundaryPairKernel K hK).ennreal_ofReal
  simpa only [Function.comp_def, extendBoundaryPairKernel_apply, boundaryPairMeasure_map_eq, boundaryPairCurrent] using h

instance boundaryPairSubgroupContinuous (Γ : Subgroup SL(2, ℝ)) : ContinuousConstSMul Γ BoundaryPair where
  continuous_const_smul g := continuous_const_smul (g : SL(2, ℝ))

/-- The current on distinct pairs is invariant when its kernel cancels the actual
stationary hitting derivatives. No pointwise positivity of derivative versions is required. -/
theorem boundaryPairCurrent_invariant_of_covariance (Γ : Subgroup SL(2, ℝ))
    (s t : Finset Γ) (μ ν : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (hν : ∀ g ∈ t, 0 < ν g)
    (hgs : Submonoid.closure (s : Set Γ) = ⊤) (hgt : Submonoid.closure (t : Set Γ) = ⊤)
    (α β : Measure (OnePoint ℝ)) [IsFiniteMeasure α] [IsFiniteMeasure β] [NullSingletonClass β]
    (hs : α = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun x : OnePoint ℝ => (g : Γ) • x) α)
    (ht : β = ∑ g : t, ENNReal.ofReal (ν g) • Measure.map (fun y : OnePoint ℝ => (g : Γ) • y) β)
    (K : BoundaryPair → ℝ) (hK : Measurable K) (g : Γ)
    (hc : ∀ᵐ p ∂boundaryPairMeasure α β, K (g⁻¹ • p) =
      K p / (stationaryRealDensity α g p.val.1 * stationaryRealDensity β g p.val.2)) :
    Measure.map (fun p : BoundaryPair => g • p) (boundaryPairCurrent α β K) =
      boundaryPairCurrent α β K := by
  have hfull : ∀ᵐ p ∂α.prod β,
      extendBoundaryPairKernel K (g⁻¹ • p.1, g⁻¹ • p.2) = extendBoundaryPairKernel K p /
        (stationaryRealDensity α g p.1 * stationaryRealDensity β g p.2) := by
    rw [← boundaryPairMeasure_map_eq α β, measurableEmbedding_boundaryPair.ae_map_iff]
    filter_upwards [hc] with p hp
    change extendBoundaryPairKernel K (g⁻¹ • p : BoundaryPair).val = _
    simpa only [extendBoundaryPairKernel_apply] using hp
  have hi := stationary_weightedProduct_invariant s t μ ν hμ hν hgs hgt α β hs ht
    (extendBoundaryPairKernel K) (measurable_extendBoundaryPairKernel K hK) g hfull
  apply measurableEmbedding_boundaryPair.map_injective
  calc
    Measure.map Subtype.val (Measure.map (fun p : BoundaryPair => g • p) (boundaryPairCurrent α β K)) =
        Measure.map (fun p : OnePoint ℝ × OnePoint ℝ => (g • p.1, g • p.2))
          (Measure.map Subtype.val (boundaryPairCurrent α β K)) := by
      have hm : Measurable (fun p : OnePoint ℝ × OnePoint ℝ => (g • p.1, g • p.2)) := by fun_prop
      rw [Measure.map_map measurable_subtype_coe (measurable_const_smul g),
        Measure.map_map hm measurable_subtype_coe]
      rfl
    _ = (α.prod β).withDensity (fun p => ENNReal.ofReal (extendBoundaryPairKernel K p)) := by
      rw [boundaryPairCurrent_map α β K hK, hi]
    _ = Measure.map Subtype.val (boundaryPairCurrent α β K) := (boundaryPairCurrent_map α β K hK).symm

end Singularity
