import Singularity.FreeGroupNonamenable
import Mathlib.GroupTheory.CoprodI
import Mathlib.Topology.Separation.Hausdorff

/-!
# Uniform north--south dynamics and free subgroups

Uniform attraction away from a repelling point supplies the ping-pong inclusions
for sufficiently large powers. Four distinct attracting/repelling points allow
pairwise disjoint neighborhoods, and Mathlib's ping-pong lemma supplies an actual
injective free-group homomorphism.
-/

noncomputable section
open Set Filter
open scoped Classical Topology Pointwise

namespace Singularity

variable {G : Type} {X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]

/-- Uniform attraction to `p` away from any neighborhood of `q`. -/
def UniformNorthSouth (g : G) (p q : X) : Prop :=
  ∀ U ∈ nhds p, ∀ V ∈ nhds q,
    ∀ᶠ n : ℕ in atTop, ∀ x ∉ V, g ^ n • x ∈ U

omit [TopologicalSpace X] in
/-- A forward ping-pong inclusion automatically gives the inverse inclusion. -/
theorem inverse_pingPong_inclusion (g : G) (U V : Set X)
    (hf : ∀ x ∉ V, g • x ∈ U) : g⁻¹ • Uᶜ ⊆ V := by
  rintro _ ⟨x, hx, rfl⟩
  by_contra hy
  have h := hf (g⁻¹ • x) hy
  simp only [smul_inv_smul] at h
  exact hx h

/-- Large common powers of two north--south elements with four distinct endpoints
freely generate a free subgroup. -/
theorem northSouth_free_powers [T2Space X] (a : Bool → G) (p q : Bool → X)
    (hdistinct : Function.Injective (fun z : Bool × Bool => if z.2 then p z.1 else q z.1))
    (hdyn : ∀ i, UniformNorthSouth (a i) (p i) (q i)) :
    ∃ n : ℕ, 0 < n ∧ Function.Injective (FreeGroup.lift (fun i => a i ^ n)) := by
  let points : Bool × Bool → X := fun z => if z.2 then p z.1 else q z.1
  obtain ⟨W, hW, hdisj⟩ := (Set.finite_range points).t2_separation
  have hmem (z : Bool × Bool) : points z ∈ Set.range points := ⟨z, rfl⟩
  have hd (z w : Bool × Bool) (hzw : z ≠ w) : Disjoint (W (points z)) (W (points w)) :=
    hdisj (hmem z) (hmem w) (fun h => hzw (hdistinct h))
  have ht : ∀ᶠ n : ℕ in atTop, ∀ i : Bool, ∀ x ∉ W (q i), a i ^ n • x ∈ W (p i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact hdyn i (W (p i)) ((hW _).2.mem_nhds (hW _).1)
      (W (q i)) ((hW _).2.mem_nhds (hW _).1)
  obtain ⟨n, hn, hnmap⟩ := ((eventually_gt_atTop 0).and ht).exists
  refine ⟨n, hn, FreeGroup.injective_lift_of_ping_pong (fun i => a i ^ n)
    (fun i => W (p i)) (fun i => W (q i)) (fun i => ⟨_, (hW _).1⟩) ?_ ?_ ?_ ?_ ?_⟩
  · intro i j hij
    exact hd (i, true) (j, true) (by simpa using hij)
  · intro i j hij
    exact hd (i, false) (j, false) (by simpa using hij)
  · intro i j
    exact hd (i, true) (j, false) (by simp)
  · intro i
    rintro _ ⟨x, hx, rfl⟩
    exact hnmap i x hx
  · intro i
    exact inverse_pingPong_inclusion (a i ^ n) _ _ (hnmap i)

/-- Uniform north--south dynamics with four distinct endpoints rules out an invariant mean. -/
theorem no_invariantMean_of_northSouth [T2Space X] (a : Bool → G) (p q : Bool → X)
    (hdistinct : Function.Injective (fun z : Bool × Bool => if z.2 then p z.1 else q z.1))
    (hdyn : ∀ i, UniformNorthSouth (a i) (p i) (q i)) : ¬HasInvariantMean G := by
  obtain ⟨n, _, hinj⟩ := northSouth_free_powers a p q hdistinct hdyn
  exact no_invariantMean_of_free_subgroup (FreeGroup.lift (fun i => a i ^ n)) hinj

end Singularity
