import Singularity.NaimAnconaBounds
import Singularity.CayleyRealBoundary
import Singularity.CocompactRayApproximation

/-!
# Off-diagonal geometric subsequences

Distinct finite real boundary approaches have positive finite subsequential
Naïm limits. For the concrete cocompact ray sequences one subsequence can also
be chosen to give positive normalized harmonic forward/reflected Martin
limits. Independence of the chosen subsequence is not asserted.
-/

noncomputable section
open Filter
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Positive finite Naïm subsequential limits for arbitrary sequences converging
to distinct finite real boundary coordinates. -/
theorem cocompact_real_boundary_naim_subsequence (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : ℕ → Γ)
    (ξ η : ℝ) (hξη : ξ ≠ η)
    (hx : Tendsto (fun n => ((x n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (ξ : ℂ)))
    (hy : Tendsto (fun n => ((y n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (η : ℂ))) :
    ∃ θ : ℝ, 0 < θ ∧ (walkGreen s μ 1 1)⁻¹ ≤ θ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => finiteNaimQuotient s μ 1 (x (φ n)) (y (φ n))) atTop (𝓝 θ) :=
  cocompact_positive_naim_subsequence Γ s μ hpos hmass hgen hgap x y
    (realBoundaryCayley ξ) (realBoundaryCayley η)
    (fun he => hξη (realBoundaryCayley_injective he))
    (halfPlaneCayley_tendsto_real _ ξ hx) (halfPlaneCayley_tendsto_real _ η hy)

/-- A common subsequence of the actual orbit rays gives a positive finite
Naïm value and normalized positive forward/reflected harmonic functions. -/
theorem cocompact_ray_naim_martin_subsequence (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (ξ η : ℝ) (hξη : ξ ≠ η) :
    ∃ (θ : ℝ) (Hm Hp : Γ → ℝ), 0 < θ ∧ Hm 1 = 1 ∧ Hp 1 = 1 ∧
      (∀ z, 0 < Hm z) ∧ (∀ z, 0 < Hp z) ∧
      (∀ z, Hm z = ∑ g ∈ s, μ g * Hm (z*g⁻¹)) ∧
      (∀ z, Hp z = ∑ g ∈ s, μ g * Hp (z*g)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => finiteNaimQuotient s μ 1 (cocompactRaySequence Γ ξ (φ n))
          (cocompactRaySequence Γ η (φ n))) atTop (𝓝 θ) ∧
        (∀ z, Tendsto (fun n => reverseMartinQuotient s μ 1 z (cocompactRaySequence Γ ξ (φ n))) atTop (𝓝 (Hm z))) ∧
        (∀ z, Tendsto (fun n => martinQuotient s μ 1 z (cocompactRaySequence Γ η (φ n))) atTop (𝓝 (Hp z))) := by
  obtain ⟨θ, hθ, _, φ, hφ, ht⟩ := cocompact_real_boundary_naim_subsequence Γ s μ hpos hmass hgen hgap
    (cocompactRaySequence Γ ξ) (cocompactRaySequence Γ η) ξ η hξη
    (cocompactRaySequence_tendsto Γ ξ) (cocompactRaySequence_tendsto Γ η)
  have hesc (ζ : ℝ) (z : Γ) : ∀ᶠ n in atTop, z ≠ cocompactRaySequence Γ ζ (φ n) :=
    hφ.tendsto_atTop.eventually ((cocompactRaySequence_eventually_ne Γ ζ z).mono (fun _ h => h.symm))
  obtain ⟨Hm, Hp, hm1, hp1, hmp, hpp, hmh, hph, ψ, hψ, hmt, hpt⟩ :=
    exists_harmonic_martinPair s μ hpos hgen hgap 1
      (fun n => cocompactRaySequence Γ ξ (φ n)) (fun n => cocompactRaySequence Γ η (φ n))
      (hesc ξ) (hesc η)
  exact ⟨θ, Hm, Hp, hθ, hm1, hp1, hmp, hpp, hmh, hph, φ ∘ ψ, hφ.comp hψ,
    ht.comp hψ.tendsto_atTop, hmt, hpt⟩

end Singularity
