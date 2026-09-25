import Singularity.QuotientFlowDuality
import Singularity.CocompactHaarMeasure
import Singularity.LiouvilleHaarMeasureClass

/-!
# Ergodicity of the actual Liouville current for a cocompact lattice

Discreteness and compactness of Γ\ℍ construct a finite Haar quotient.
The checked Mautner argument proves diagonal-time ergodicity there. Measurable
set descent and the Haar–Liouville measure-class correspondence transfer this
to the lattice action on the concrete ordered boundary-pair current.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- A discrete cocompact Fuchsian group acts ergodically on the concrete Liouville current. -/
theorem compactLiouvilleCurrent_ergodic (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    ErgodicSMul Γ BoundaryPair compactLiouvilleCurrent := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  borelize SL(2, ℝ)
  let ν : Measure SL(2, ℝ) := Measure.haar
  let := slTwo_haar_rightInvariant ν
  let : Countable Γ := countable_of_Lindelof_of_discrete
  let := cocompactHaarQuotientMeasure_formula Γ ν
  let := compactLiouvilleCurrent_subgroupInvariant Γ
  exact ergodicSMul_of_quotient_flow Γ ν (cocompactHaarQuotientMeasure Γ ν)
    (cocompactHaarDomain_fundamental Γ ν) compactLiouvilleCurrent
    inverseFrameEndpoints measurable_inverseFrameEndpoints
    (inverseFrameEndpoints_measureClass ν) inverseFrameEndpoints_mul
    (dilationMatrix 1) (inverseFrameEndpoints_dilation 1)
    (cocompactHaarQuotientMeasure_dilation_ergodic Γ ν 1 (by norm_num))

end Singularity
