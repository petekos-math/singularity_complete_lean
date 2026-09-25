import Singularity.CocompactRayApproximation
import Singularity.SLTwoHaar
import Singularity.CompactFundamentalDomain
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction

/-!
# From a compact surface quotient to a finite group fundamental domain

Properness of the orbit map SL(2,ℝ) → ℍ lifts a compact orbit-covering set to
a compact set of matrices. Inversion changes the left covering into a right
coset covering. The measurable-transversal construction then supplies the
finite Haar fundamental domain needed by the Mautner argument.
-/

noncomputable section
open Set MeasureTheory Topology
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- Compactness of Γ\ℍ implies compactness of the right-coset quotient SL(2,ℝ)/Γ. -/
theorem cocompact_slTwo_quotient (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    CompactSpace (SL(2, ℝ) ⧸ Γ) := by
  obtain ⟨K, hK, hcover⟩ := exists_compact_orbit_cover Γ
  let L : Set SL(2, ℝ) := (fun g : SL(2, ℝ) => g • UpperHalfPlane.I) ⁻¹' K
  have hL : IsCompact L := UpperHalfPlane.isProperMap_smul_I.isCompact_preimage hK
  have hi : IsCompact (Inv.inv '' L) := hL.image continuous_inv
  have hπ : (QuotientGroup.mk : SL(2, ℝ) → SL(2, ℝ) ⧸ Γ) '' (Inv.inv '' L) = univ := by
    apply eq_univ_iff_forall.mpr
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨γ, hγ⟩ := hcover (g⁻¹ • UpperHalfPlane.I)
    refine ⟨((γ : SL(2, ℝ)) * g⁻¹)⁻¹, ⟨_, ?_, rfl⟩, ?_⟩
    · change ((γ : SL(2, ℝ)) * g⁻¹) • UpperHalfPlane.I ∈ K
      rw [mul_smul]
      change (γ : SL(2, ℝ)) • (g⁻¹ • UpperHalfPlane.I) ∈ K at hγ
      exact hγ
    · simp only [mul_inv_rev, inv_inv]
      exact QuotientGroup.mk_mul_of_mem g (Γ.inv_mem γ.property)
  exact ⟨hπ ▸ hi.image continuous_quotient_mk'⟩

/-- The actual cocompact surface hypothesis supplies a finite Haar fundamental domain. -/
theorem exists_cocompact_finite_fundamentalDomain
    [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    (ν : Measure SL(2, ℝ)) [IsLocallyFiniteMeasure ν] :
    ∃ S : Set SL(2, ℝ), MeasurableSet S ∧ IsFundamentalDomain Γ.op S ν ∧ ν S < ⊤ := by
  let := slTwo_locallyCompactSpace
  let := slTwo_polishSpace
  let := cocompact_slTwo_quotient Γ
  exact exists_finite_fundamentalDomain Γ ν

end Singularity
