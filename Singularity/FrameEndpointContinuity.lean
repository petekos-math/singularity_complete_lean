import Singularity.FrameCoordinates

/-!
# Continuity of frame endpoints

The fractional-linear formula is continuous near the identity in a finite
boundary chart. A fixed coordinate change handles infinity, and translation
handles every group element. Consequently a compact family of frames has a
compact set of ordered endpoint pairs.
-/

noncomputable section
open OnePoint Filter
open scoped MatrixGroups Topology

namespace Singularity

/-- The boundary orbit map is continuous at the identity for every finite point. -/
theorem continuousAt_compactBoundary_orbit_coe_one (x : ℝ) :
    ContinuousAt (fun g : SL(2, ℝ) => g • (x : OnePoint ℝ)) 1 := by
  have hc (i j : Fin 2) : Continuous (fun g : SL(2, ℝ) => g i j) :=
    continuous_subtype_val.matrix_elem i j
  have hden : (1 : SL(2, ℝ)) 1 0 * x + (1 : SL(2, ℝ)) 1 1 ≠ 0 := by simp
  have hr : ContinuousAt (fun g : SL(2, ℝ) => (g 0 0 * x + g 0 1) / (g 1 0 * x + g 1 1)) 1 :=
    (((hc 0 0).mul_const x).add (hc 0 1)).continuousAt.div
      (((hc 1 0).mul_const x).add (hc 1 1)).continuousAt hden
  have hh := OnePoint.continuous_coe.continuousAt.tendsto.comp hr.tendsto
  have he : (fun g : SL(2, ℝ) => (((g 0 0 * x + g 0 1) / (g 1 0 * x + g 1 1) : ℝ) : OnePoint ℝ)) =ᶠ[𝓝 1]
      fun g => g • (x : OnePoint ℝ) := by
    filter_upwards [(((hc 1 0).mul_const x).add (hc 1 1)).continuousAt.eventually_ne hden] with g hg
    change g 1 0 * x + g 1 1 ≠ 0 at hg
    simp [compactBoundary_smul_coe_formula, hg]
  simpa [ContinuousAt] using hh.congr' he

/-- Continuity at the identity includes the point at infinity. -/
theorem continuousAt_compactBoundary_orbit_one (p : OnePoint ℝ) :
    ContinuousAt (fun g : SL(2, ℝ) => g • p) 1 := by
  cases p with
  | coe x => exact continuousAt_compactBoundary_orbit_coe_one x
  | infty =>
    let S : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp⟩
    have hS : S • ((0 : ℝ) : OnePoint ℝ) = ∞ := by
      rw [compactBoundary_smul_coe_formula]
      simp [S]
    have hc : Tendsto (fun g : SL(2, ℝ) => S⁻¹ * g * S) (𝓝 1) (𝓝 1) := by
      simpa using ((continuous_id.const_mul S⁻¹).mul_const S).tendsto (1 : SL(2, ℝ))
    have hh := (continuousAt_compactBoundary_orbit_coe_one 0).tendsto.comp hc
    have ho := (continuous_const_smul S).continuousAt.tendsto.comp hh
    simpa only [ContinuousAt, Function.comp_def, mul_smul, hS, smul_inv_smul, one_smul] using ho

/-- The orbit of a fixed boundary point depends continuously on the matrix. -/
theorem continuous_compactBoundary_orbit (p : OnePoint ℝ) :
    Continuous (fun g : SL(2, ℝ) => g • p) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hc : Tendsto (fun g : SL(2, ℝ) => g * a⁻¹) (𝓝 a) (𝓝 1) := by
    simpa using (continuous_id.mul_const a⁻¹).tendsto a
  have hh := (continuousAt_compactBoundary_orbit_one (a • p)).tendsto.comp hc
  simpa only [ContinuousAt, Function.comp_def, mul_smul, inv_smul_smul, one_smul] using hh

/-- The inverse-frame endpoint projection is continuous on the whole frame group. -/
theorem continuous_inverseFrameEndpoints : Continuous inverseFrameEndpoints := by
  apply Continuous.subtype_mk
  exact ((continuous_compactBoundary_orbit (∞ : OnePoint ℝ)).comp continuous_inv).prodMk
    ((continuous_compactBoundary_orbit ((0 : ℝ) : OnePoint ℝ)).comp continuous_inv)

/-- Contracting lower horocycles preserve the forward endpoint in our convention. -/
theorem inverseFrameEndpoints_lowerShear_forward (u : ℝ) (g : SL(2, ℝ)) :
    (inverseFrameEndpoints (lowerShearMatrix u * g)).val.2 = (inverseFrameEndpoints g).val.2 := by
  have h0 : (lowerShearMatrix u)⁻¹ • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by
    rw [lowerShearMatrix_inv, compactBoundary_smul_coe_formula]
    simp [lowerShearMatrix]
  change (lowerShearMatrix u * g)⁻¹ • ((0 : ℝ) : OnePoint ℝ) = g⁻¹ • ((0 : ℝ) : OnePoint ℝ)
  rw [mul_inv_rev, mul_smul, h0]

end Singularity
