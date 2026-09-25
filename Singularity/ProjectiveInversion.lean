import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Inversion on the compact projective line

Inversion exchanges zero and infinity. Unlike field inversion with a totalized
zero value, this map is continuous on the one-point compactification. The
construction works over both the real and complex fields.
-/

noncomputable section
open Filter Set OnePoint
open scoped Topology Classical

namespace Singularity

variable {K : Type*} [NontriviallyNormedField K]

/-- Projective inversion, including its values at zero and infinity. -/
def projectiveInv (p : OnePoint K) : OnePoint K :=
  p.elim (0 : K) (fun x => if x = 0 then ∞ else ((x⁻¹ : K) : OnePoint K))

theorem projectiveInv_infty : projectiveInv (∞ : OnePoint K) = (0 : K) := rfl

theorem projectiveInv_coe (x : K) :
    projectiveInv (x : OnePoint K) = if x = 0 then ∞ else ((x⁻¹ : K) : OnePoint K) := rfl

theorem projectiveInv_zero : projectiveInv ((0 : K) : OnePoint K) = ∞ := by
  simp [projectiveInv_coe]

/-- The extension is an involution at every projective point. -/
theorem projectiveInv_involutive : Function.Involutive (projectiveInv (K := K)) := by
  intro p
  cases p with
  | infty => simp [projectiveInv_infty, projectiveInv_zero]
  | coe x =>
    by_cases hx : x = 0
    · subst x; simp [projectiveInv_zero, projectiveInv_infty]
    · simp [projectiveInv_coe, hx, inv_ne_zero hx]

variable [ProperSpace K]

/-- Near zero, punctured field inversion tends to the projective point at infinity. -/
theorem projectiveInv_tendsto_zero :
    Tendsto (fun x : K => projectiveInv (x : OnePoint K)) (nhdsWithin 0 {0}ᶜ)
      (nhds (∞ : OnePoint K)) := by
  have h := (OnePoint.tendsto_coe_infty (X := K)).comp
    (show Tendsto (Inv.inv : K → K) (nhdsWithin 0 {0}ᶜ) (coclosedCompact K) by
      simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        using (tendsto_inv₀_nhdsNE_zero (α := K)))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [mem_compl_iff, mem_singleton_iff] at hx
  simp [projectiveInv_coe, hx]

/-- Projective inversion is continuous on the whole compactification. -/
theorem continuous_projectiveInv : Continuous (projectiveInv (K := K)) := by
  rw [OnePoint.continuous_iff]
  constructor
  · have h := OnePoint.continuous_coe.continuousAt.tendsto.comp
      (show Tendsto (Inv.inv : K → K) (coclosedCompact K) (nhds 0) by
        simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
          using (tendsto_inv₀_cobounded (α := K)))
    change Tendsto _ _ (nhds ((0 : K) : OnePoint K))
    apply h.congr'
    have hz : ∀ᶠ x : K in coclosedCompact K, x ≠ 0 :=
      (hasBasis_coclosedCompact.mem_iff.mpr ⟨{0}, ⟨isClosed_singleton, isCompact_singleton⟩,
        fun x hx => hx⟩)
    filter_upwards [hz] with x hx
    simp [projectiveInv_coe, hx]
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst x
      rw [continuousAt_iff_punctured_nhds, projectiveInv_zero]
      exact projectiveInv_tendsto_zero
    · have h := OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hx)
      apply h.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [projectiveInv_coe, hy]

/-- Inversion is a homeomorphism of the compact projective line. -/
def projectiveInvHomeomorph : OnePoint K ≃ₜ OnePoint K where
  toEquiv := Function.Involutive.toPerm projectiveInv projectiveInv_involutive
  continuous_toFun := continuous_projectiveInv
  continuous_invFun := continuous_projectiveInv

end Singularity
