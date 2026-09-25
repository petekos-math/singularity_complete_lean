import Singularity.FuchsianVisualShadowCover

/-!
# Adding visual shadows to an exceptional-set shadow family

The visual exceptional-point convergence is proved internally. Along a
subsequence it can be combined with a second family's exceptional-set data.
The resulting mixed family has a finite corrected eventual cover when the
second exceptional set is finite. Only the second family's data remain inputs.
-/

noncomputable section
open Set Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology

namespace Singularity

/-- Intersecting with actual visual shadows adds at most one exceptional
point after passing to a subsequence. -/
theorem mixed_visualShadow_exceptional_subsequence {I : Type*}
    (g : ℕ → PSL(2, ℝ)) (z : ℍ) (S : I → ℕ → Set (OnePoint ℝ)) (Z : Set (OnePoint ℝ))
    (hS : ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ i : I,
      ∀ᶠ n in atTop, ((fun ξ : OnePoint ℝ => g n • ξ) ⁻¹' S i n)ᶜ ⊆ U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : OnePoint ℝ,
      ∀ U : Set (OnePoint ℝ), IsOpen U → Z ∪ {p} ⊆ U →
        ∃ i : I, ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
          ((fun ξ : OnePoint ℝ => g (φ n) • ξ) ⁻¹'
            (S i (φ n) ∩ visualShadow z (g (φ n) • z) r))ᶜ ⊆ U := by
  obtain ⟨φ, hφ, p, hp⟩ := projective_visualShadow_exceptional_subsequence g z
  refine ⟨φ, hφ, p, fun U hU hZU => ?_⟩
  obtain ⟨i, hi⟩ := hS U hU (subset_union_left.trans hZU)
  obtain ⟨r, hr, hv⟩ := hp U hU (hZU (Or.inr (mem_singleton p)))
  refine ⟨i, r, hr, ?_⟩
  filter_upwards [hφ.tendsto_atTop.eventually hi, hv] with n hn hvn
  rw [preimage_inter, compl_inter]
  exact union_subset hn hvn

/-- The topological mixed-shadow coverage for a nonelementary Fuchsian group.
The visual part is established internally; the second family's adjustable
exceptional-set convergence is the remaining hypothesis. -/
theorem fuchsian_mixed_visualShadow_finite_eventual_cover {I : Type*}
    (Γ : Subgroup PSL(2, ℝ)) (hne : ProjectiveNonelementary Γ)
    (g : ℕ → Γ) (z : ℍ) (S : I → ℕ → Set (OnePoint ℝ)) {Z : Set (OnePoint ℝ)}
    (hZ : Z.Finite)
    (hS : ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ i : I,
      ∀ᶠ n in atTop, ((fun ξ : OnePoint ℝ => g n • ξ) ⁻¹' S i n)ᶜ ⊆ U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ i : I, ∃ r : ℝ, 0 < r ∧ ∃ F : Finset Γ,
      ∀ ξ : OnePoint ℝ, ∃ a ∈ F, ∀ᶠ n in atTop,
        g (φ n) • (a⁻¹ • ξ) ∈ S i (φ n) ∩ visualShadow z (g (φ n) • z) r := by
  obtain ⟨φ, hφ, p, hp⟩ := mixed_visualShadow_exceptional_subsequence
    (fun n => (g n : PSL(2, ℝ))) z S Z hS
  have hfinite : (Z ∪ {p}).Finite := hZ.union (finite_singleton p)
  have hescape (ξ : OnePoint ℝ) : ∃ a : Γ, a⁻¹ • ξ ∉ Z ∪ {p} := by
    by_contra hnone
    push Not at hnone
    apply hne.infinite_boundary_orbits Γ ξ
    apply hfinite.subset
    rintro η ⟨a, rfl⟩
    simpa only [inv_inv] using hnone a⁻¹
  obtain ⟨U, hU, hZU, F, hF⟩ := finite_corrections_avoid_exceptional_neighborhood
    (Z ∪ {p}) hfinite.isClosed hescape
  obtain ⟨i, r, hr, hex⟩ := hp U hU hZU
  refine ⟨φ, hφ, i, r, hr, F, fun ξ => ?_⟩
  obtain ⟨a, ha, hnot⟩ := hF ξ
  refine ⟨a, ha, ?_⟩
  filter_upwards [hex] with n hn
  by_contra hbad
  exact hnot (hn hbad)

end Singularity
