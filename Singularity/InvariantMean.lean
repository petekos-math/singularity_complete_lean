import Singularity.L2InvariantMean

/-!
# The nonamenability criterion for the right Markov operator

Amenability is expressed here by the classical existence of a nonnegative,
normalized, finitely additive invariant probability on every subset of the group.
Inversion identifies left and right invariant means. Absence of such a mean
therefore implies the spectral gap for the actual right Markov operator, under
positive finite support and semigroup generation. No laziness or symmetry is
required. Nonamenability of the relevant Fuchsian subgroups is a separate input.
-/

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Singularity

/-- The classical set-function definition of an invariant mean on a discrete group. -/
def HasInvariantMean (Γ : Type*) [Group Γ] : Prop :=
  ∃ m : Set Γ → ℝ, (∀ A, 0 ≤ m A) ∧ m ∅ = 0 ∧ m univ = 1 ∧
    (∀ A B, Disjoint A B → m (A ∪ B) = m A + m B) ∧
    ∀ g : Γ, ∀ A, m ((fun x => g * x) '' A) = m A

/-- Inversion identifies the left and right versions of invariant means. -/
theorem hasInvariantMean_iff_right (Γ : Type*) [Group Γ] :
    HasInvariantMean Γ ↔ HasRightInvariantMean Γ := by
  have hdisj (A B : Set Γ) (hAB : Disjoint A B) : Disjoint (Inv.inv '' A) (Inv.inv '' B) :=
    hAB.image (inv_injective.injOn (s := Set.univ)) (Set.subset_univ A) (Set.subset_univ B)
  constructor
  · rintro ⟨m, hpos, hemp, huniv, hadd, hinv⟩
    refine ⟨fun A => m (Inv.inv '' A), fun A => hpos _, ?_, ?_, ?_, ?_⟩
    · simpa only [image_empty] using hemp
    · simpa only [Set.image_univ_of_surjective inv_surjective] using huniv
    · intro A B hAB
      dsimp only
      rw [image_union]
      exact hadd _ _ (hdisj A B hAB)
    · intro g A
      have he : Inv.inv '' ((fun x => x * g) '' A) =
          (fun x => g⁻¹ * x) '' (Inv.inv '' A) := by
        rw [image_image, image_image]
        congr 1
        funext x
        exact mul_inv_rev x g
      dsimp only
      rw [he]
      exact hinv g⁻¹ _
  · rintro ⟨m, hpos, hemp, huniv, hadd, hinv⟩
    refine ⟨fun A => m (Inv.inv '' A), fun A => hpos _, ?_, ?_, ?_, ?_⟩
    · simpa only [image_empty] using hemp
    · simpa only [Set.image_univ_of_surjective inv_surjective] using huniv
    · intro A B hAB
      dsimp only
      rw [image_union]
      exact hadd _ _ (hdisj A B hAB)
    · intro g A
      have he : Inv.inv '' ((fun x => g * x) '' A) =
          (fun x => x * g⁻¹) '' (Inv.inv '' A) := by
        rw [image_image, image_image]
        congr 1
        funext x
        exact mul_inv_rev g x
      dsimp only
      rw [he]
      exact hinv g⁻¹ _

/-- Nonamenability implies spectral radius strictly below one for the right walk.
The support is finite, positive, and generates the whole group as a semigroup. -/
theorem rightMarkov_nonamenable_spectral_gap {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hnon : ¬HasInvariantMean Γ) : spectralRadius ℂ (rightMarkov s μ) < 1 :=
  rightMarkov_gap_of_no_rightInvariantMean s μ hpos hmass hgen
    (fun h => hnon ((hasInvariantMean_iff_right Γ).mpr h))

end Singularity
