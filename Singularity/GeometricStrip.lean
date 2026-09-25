import Singularity.StripOrbits
import Singularity.StripSeparation

/-!
# A finite periodic separator for an actual discrete subgroup

For a finite jump set we choose an explicit length bound and coordinate strip.
This strip separates opposite boundary sides and is a finite disjoint union of
cyclic orbits for any normalized diagonal element in the subgroup.
-/

noncomputable section
open Set
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

/-- The sum of finitely many jump lengths is a convenient common upper bound. -/
def finiteJumpLengthBound (Γ : Subgroup SL(2, ℝ)) (z : ℍ) (s : Finset Γ) : ℝ :=
  ∑ t ∈ s, dist z (t • z)

theorem finiteJumpLengthBound_nonneg (Γ : Subgroup SL(2, ℝ)) (z : ℍ) (s : Finset Γ) :
    0 ≤ finiteJumpLengthBound Γ z s := Finset.sum_nonneg (fun _ _ => dist_nonneg)

theorem dist_le_finiteJumpLengthBound (Γ : Subgroup SL(2, ℝ)) (z : ℍ)
    (s : Finset Γ) {t : Γ} (ht : t ∈ s) : dist z (t • z) ≤ finiteJumpLengthBound Γ z s := by
  unfold finiteJumpLengthBound
  exact Finset.single_le_sum (f := fun t : Γ => dist z (t • z)) (fun _ _ => dist_nonneg) ht

/-- The actual group-vertex strip chosen from a finite jump law. -/
def finiteJumpStrip (Γ : Subgroup SL(2, ℝ)) (z : ℍ) (s : Finset Γ) : Set Γ :=
  {g | g • z ∈ axisRatioStrip (jumpStripRadius (finiteJumpLengthBound Γ z s))}

/-- The chosen strip meets every allowed path between opposite sides. -/
theorem finiteJumpStrip_separates (Γ : Subgroup SL(2, ℝ)) (z : ℍ) (s : Finset Γ)
    (x y : Γ) (hx : (x • z).re < 0) (hy : 0 ≤ (y • z).re) :
    SeparatesJumpPaths s (finiteJumpStrip Γ z s) x y :=
  axisRatioStrip_separatesJumpPaths Γ z s (finiteJumpLengthBound_nonneg Γ z s)
    (fun _ ht => dist_le_finiteJumpLengthBound Γ z s ht) x y hx hy

/-- With the base point i, the identity belongs to the chosen strip. -/
theorem one_mem_finiteJumpStrip (Γ : Subgroup SL(2, ℝ)) (s : Finset Γ) :
    (1 : Γ) ∈ finiteJumpStrip Γ UpperHalfPlane.I s := by
  change |((1 : Γ) • UpperHalfPlane.I).re / ((1 : Γ) • UpperHalfPlane.I).im| ≤ _
  simp only [one_smul, UpperHalfPlane.I_re, UpperHalfPlane.I_im, zero_div, abs_zero]
  exact (jumpStripRadius_pos (finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s)).le

/-- A nonempty finite disjoint cyclic decomposition of the actual separator.
All finiteness and path-separation assertions are conclusions, not hypotheses. -/
theorem finiteJumpStrip_finite_cyclic_decomposition
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] (s : Finset Γ)
    (a : Γ) {τ : ℝ} (ha : (a : SL(2, ℝ)) = dilationMatrix τ) (hτ : 0 < τ) :
    ∃ (N : ℕ), 0 < N ∧ ∃ (b : Fin N → Γ),
      Function.Injective (fun p : ℤ × Fin N => a ^ p.1 * b p.2) ∧
      finiteJumpStrip Γ UpperHalfPlane.I s = cyclicOrbitUnion a b ∧
      ∀ x y : Γ, (x • UpperHalfPlane.I).re < 0 → 0 ≤ (y • UpperHalfPlane.I).re →
        SeparatesJumpPaths s (cyclicOrbitUnion a b) x y := by
  obtain ⟨N, b, hinj, he⟩ := exists_finite_strip_orbits Γ a ha hτ UpperHalfPlane.I
    (jumpStripRadius_pos (finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s)).le
  change finiteJumpStrip Γ UpperHalfPlane.I s = cyclicOrbitUnion a b at he
  have hmem : (1 : Γ) ∈ cyclicOrbitUnion a b := he ▸ one_mem_finiteJumpStrip Γ s
  obtain ⟨⟨n, j⟩, _⟩ := hmem
  refine ⟨N, Nat.zero_lt_of_lt j.isLt, b, hinj, he, ?_⟩
  intro x y hx hy
  rw [← he]
  exact finiteJumpStrip_separates Γ UpperHalfPlane.I s x y hx hy

end Singularity
