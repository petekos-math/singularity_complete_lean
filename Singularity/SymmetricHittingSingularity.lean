import Singularity.CocompactTwoSidedSingularity

/-!
# Singularity for symmetric finite-support cocompact walks

For an inversion-invariant jump set and symmetric weights, the reflected walk
has exactly the same actual hitting measure. The two-sided singularity theorem
then gives singularity of that measure itself.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

/-- Reflection leaves the actual hitting law unchanged for a symmetric jump law. -/
theorem reflectedGeometricHittingMeasure_eq_of_symmetric
    (hs : s.map ⟨Inv.inv, inv_injective⟩ = s) (hμ : ∀ g ∈ s, μ g⁻¹ = μ g) (z : ℍ) :
    reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z =
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z := by
  have hcongr (t : Finset Γ) (w : Γ → ℝ) (hp : ∀ g ∈ t, 0 < w g)
      (hm : ∑ g ∈ t, w g = 1) (hg : Submonoid.closure (t : Set Γ) = ⊤)
      (hr : spectralRadius ℂ (rightMarkov t w) < 1) (ht : t = s) (hw : ∀ g ∈ s, w g = μ g) :
      geometricHittingMeasure Γ t w hp hm hg hr z = geometricHittingMeasure Γ s μ hpos hmass hgen hgap z := by
    subst t
    have h := geometricHittingMeasure_transport Γ Γ s s (Equiv.refl s) w μ hp hpos hm hmass hg hgen hr hgap
      (fun g => (hw g g.property).symm) (MonoidHom.id Γ) (fun _ => rfl) 1
      (fun _ _ => by simp) z
    simp only [one_smul] at h
    change geometricHittingMeasure Γ s μ hpos hmass hgen hgap z =
      Measure.map id (geometricHittingMeasure Γ s w hp hm hg hr z) at h
    rw [Measure.map_id] at h
    exact h.symm
  exact hcongr _ _ (reflected_jump_pos s μ hpos) ((reflected_jump_mass s μ).trans hmass)
    (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap) hs hμ

variable [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)

include horbit in
/-- The actual symmetric finite-support hitting measure of a discrete cocompact
group with infinite boundary orbits is singular with respect to visual measure. -/
theorem cocompact_symmetric_hittingMeasure_singular
    (hs : s.map ⟨Inv.inv, inv_injective⟩ = s) (hμ : ∀ g ∈ s, μ g⁻¹ = μ g) (z : ℍ) :
    geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ⟂ₘ compactPoissonMeasure z := by
  have h := cocompact_forward_or_reflected_singular Γ s μ hpos hmass hgen hgap horbit z
  rw [reflectedGeometricHittingMeasure_eq_of_symmetric Γ s μ hpos hmass hgen hgap hs hμ z] at h
  exact h.elim id id

/-- The symmetric conclusion needs no separately assumed spectral gap. -/
theorem cocompact_symmetric_hittingMeasure_singular_of_infinite_orbits
    (hs : s.map ⟨Inv.inv, inv_injective⟩ = s) (hμ : ∀ g ∈ s, μ g⁻¹ = μ g) (z : ℍ) :
    geometricHittingMeasure Γ s μ hpos hmass hgen
      (rightMarkov_gap_of_cocompact Γ horbit s μ hpos hmass hgen) z ⟂ₘ compactPoissonMeasure z :=
  cocompact_symmetric_hittingMeasure_singular Γ s μ hpos hmass hgen
    (rightMarkov_gap_of_cocompact Γ horbit s μ hpos hmass hgen) horbit hs hμ z

end Singularity
