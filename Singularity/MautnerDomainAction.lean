import Singularity.MautnerSLTwo
import Mathlib.Topology.Algebra.Constructions.DomMulAct

/-!
# Mautner's conclusion for precomposition actions

Precomposition reverses multiplication. The inverse map identifies the group
with its domain-action opposite; transporting the action gives the usual
Mautner conclusion without assuming that the group is commutative.
-/

noncomputable section
open scoped MatrixGroups

namespace Singularity

/-- Inversion, interpreted as a homomorphism into the domain-action opposite. -/
def inverseDomainHom (G : Type*) [Group G] : G →* Gᵈᵐᵃ where
  toFun g := DomMulAct.mk g⁻¹
  map_one' := by simp
  map_mul' a b := by simp

theorem continuous_inverseDomainHom {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : Continuous (inverseDomainHom G) :=
  DomMulAct.continuous_mk.comp continuous_inv

/-- The fixed-vector theorem also holds for the opposite action used on function spaces. -/
theorem fixed_domain_slTwo_of_fixed_dilation {X : Type*} [MetricSpace X]
    [MulAction SL(2, ℝ)ᵈᵐᵃ X] [IsIsometricSMul SL(2, ℝ)ᵈᵐᵃ X]
    [ContinuousSMul SL(2, ℝ)ᵈᵐᵃ X] (τ : ℝ) (hτ : 0 < τ)
    (v : X) (hfix : DomMulAct.mk (dilationMatrix τ) • v = v) (g : SL(2, ℝ)) :
    DomMulAct.mk g • v = v := by
  let : MulAction SL(2, ℝ) X := MulAction.compHom X (inverseDomainHom SL(2, ℝ))
  let : IsIsometricSMul SL(2, ℝ) X :=
    ⟨fun g => isometry_smul X (DomMulAct.mk g⁻¹)⟩
  let : ContinuousSMul SL(2, ℝ) X :=
    MulAction.continuousSMul_compHom continuous_inverseDomainHom
  have hf : dilationMatrix τ • v = v := by
    change (DomMulAct.mk (dilationMatrix τ))⁻¹ • v = v
    exact inv_smul_eq_iff.mpr hfix.symm
  have hg := fixed_slTwo_of_fixed_dilation τ hτ v hf g⁻¹
  change DomMulAct.mk (g⁻¹)⁻¹ • v = v at hg
  simpa only [inv_inv] using hg

end Singularity
