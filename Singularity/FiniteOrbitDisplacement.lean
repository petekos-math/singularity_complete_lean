import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Moving a finite set away from another finite set

B. H. Neumann's coset-cover lemma implies that a finite collection of points
with infinite orbits can be translated away from any prescribed finite set.
This supplies disjoint endpoint pairs for the north--south argument.
-/

noncomputable section
open Set MulAction
open scoped Classical Pointwise

namespace Singularity

/-- A finite set of points with infinite orbits has a translate avoiding any finite set. -/
theorem exists_translate_disjoint_of_infinite_orbits {G X : Type*} [Group G] [MulAction G X]
    (S T : Set X) (hS : S.Finite) (hT : T.Finite)
    (hinf : ∀ x ∈ S, (MulAction.orbit G x).Infinite) :
    ∃ g : G, Disjoint ((fun x => g • x) '' S) T := by
  classical
  let : Fintype S := hS.fintype
  let : Fintype T := hT.fintype
  let I := {z : S × T // ∃ g : G, g • (z.1 : X) = (z.2 : X)}
  let : Fintype I := Fintype.ofFinite I
  let r : I → G := fun z => z.property.choose
  have hr (z : I) : r z • (z.val.1 : X) = (z.val.2 : X) := z.property.choose_spec
  let H : I → Subgroup G := fun z => MulAction.stabilizer G (z.val.1 : X)
  by_contra h
  push Not at h
  have hcov : ⋃ z ∈ (Finset.univ : Finset I), r z • (H z : Set G) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨y, ⟨x, hx, hxy⟩, hy⟩ := Set.not_disjoint_iff.mp (h g)
    let z : I := ⟨(⟨x, hx⟩, ⟨y, hy⟩), g, hxy⟩
    apply Set.mem_iUnion.mpr ⟨z, ?_⟩
    apply Set.mem_iUnion.mpr ⟨Finset.mem_univ z, ?_⟩
    refine ⟨(r z)⁻¹ * g, ?_, by simp⟩
    change ((r z)⁻¹ * g) • x = x
    change g • x = y at hxy
    rw [mul_smul, hxy]
    have hz : r z • x = y := hr z
    rw [← hz, inv_smul_smul]
  obtain ⟨z, _, hz⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcov
  let : (H z).FiniteIndex := hz
  let : Finite (G ⧸ MulAction.stabilizer G (z.val.1 : X)) :=
    Subgroup.finite_quotient_of_finiteIndex
  let : Finite (MulAction.orbit G (z.val.1 : X)) :=
    Finite.of_equiv (G ⧸ MulAction.stabilizer G (z.val.1 : X))
      (MulAction.orbitEquivQuotientStabilizer G (z.val.1 : X)).symm
  exact hinf z.val.1 z.val.1.property (Set.toFinite _)

end Singularity
