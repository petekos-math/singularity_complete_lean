import Singularity.HittingBasepoint
import Singularity.WalkTransport
import Singularity.BoundaryConjugacy

/-!
# Conjugacy of the actual geometric hitting laws

The change of coordinates acts on the genuine product path law. Uniqueness of
compact limits identifies the chosen boundary maps almost everywhere, hence
identifies their pushforward measures exactly.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ Λ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] [DiscreteTopology Λ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  [MeasurableSpace Λ] [MeasurableSingletonClass Λ] [MeasurableMul Λ]
  (s : Finset Γ) (t : Finset Λ) (e : s ≃ t)
  (μ : Γ → ℝ) (ν : Λ → ℝ)
  (hμ : ∀ g ∈ s, 0 < μ g) (hν : ∀ g ∈ t, 0 < ν g)
  (hm : ∑ g ∈ s, μ g = 1) (hn : ∑ g ∈ t, ν g = 1)
  (hgs : Submonoid.closure (s : Set Γ) = ⊤)
  (hgt : Submonoid.closure (t : Set Λ) = ⊤)
  (hrs : spectralRadius ℂ (rightMarkov s μ) < 1)
  (hrt : spectralRadius ℂ (rightMarkov t ν) < 1)
  (hw : ∀ g : s, ν (e g) = μ g)
  (φ : Γ →* Λ) (he : ∀ g : s, (e g : Λ) = φ g)
  (B : SL(2, ℝ)) (ha : ∀ (g : Γ) (z : ℍ), B • (g • z) = φ g • (B • z))

include hw he ha

/-- Relabeled sample limits are the conjugated original limits almost surely. -/
theorem geometricBoundaryMap_transport_ae (z : ℍ) :
    (fun ω => geometricBoundaryMap Λ t ν hν hn hgt hrt (B • z) (transportWalk s t e ω))
      =ᵐ[infiniteWalkLaw s μ (fun g hg => (hμ g hg).le) hm]
    (fun ω => B • geometricBoundaryMap Γ s μ hμ hm hgs hrs z ω) := by
  have ht := geometricBoundaryMap_tendsto Λ t ν hν hn hgt hrt (B • z)
  rw [← infiniteWalkLaw_transport s t e μ ν
    (fun g hg => (hμ g hg).le) (fun g hg => (hν g hg).le) hm hn hw] at ht
  have ht' := ae_of_ae_map (measurable_transportWalk s t e).aemeasurable ht
  filter_upwards [ht', geometricBoundaryMap_tendsto Γ s μ hμ hm hgs hrs z] with ω htω hsω
  have hb := (continuous_const_smul B).continuousAt.tendsto.comp hsω
  have hp : (fun n => hyperbolicCompactEmbedding
      (walkPosition t 1 n (transportWalk s t e ω) • (B • z))) =
      (fun n => B • hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) := by
    funext n
    rw [← φ.map_one, walkPosition_transport s t e φ he, ← ha]
    exact hyperbolicCompactEmbedding_smul B _
  rw [hp] at htω
  have hu := tendsto_nhds_unique htω hb
  rw [← compactBoundaryEmbedding_smul] at hu
  exact compactBoundaryEmbedding_injective hu

/-- The actual hitting law of the relabeled walk is the boundary pushforward. -/
theorem geometricHittingMeasure_transport (z : ℍ) :
    geometricHittingMeasure Λ t ν hν hn hgt hrt (B • z) =
      Measure.map (fun p : OnePoint ℝ => B • p)
        (geometricHittingMeasure Γ s μ hμ hm hgs hrs z) := by
  unfold geometricHittingMeasure walkBoundaryLaw
  rw [← infiniteWalkLaw_transport s t e μ ν
    (fun g hg => (hμ g hg).le) (fun g hg => (hν g hg).le) hm hn hw,
    Measure.map_map (measurable_geometricBoundaryMap Λ t ν hν hn hgt hrt (B • z))
      (measurable_transportWalk s t e),
    Measure.map_map (measurable_const_smul B)
      (measurable_geometricBoundaryMap Γ s μ hμ hm hgs hrs z)]
  exact Measure.map_congr
    (geometricBoundaryMap_transport_ae Γ Λ s t e μ ν hμ hν hm hn hgs hgt hrs hrt hw φ he B ha z)

/-- Visual singularity is preserved and reflected for the actual transported walks. -/
theorem geometricHittingMeasure_transport_singularity_iff (z : ℍ) :
    geometricHittingMeasure Λ t ν hν hn hgt hrt (B • z) ⟂ₘ compactPoissonMeasure (B • z) ↔
      geometricHittingMeasure Γ s μ hμ hm hgs hrs z ⟂ₘ compactPoissonMeasure z := by
  rw [geometricHittingMeasure_transport Γ Λ s t e μ ν hμ hν hm hn hgs hgt hrs hrt hw φ he B ha]
  exact compactBoundary_visual_singularity_conjugacy B _ z

/-- Both walks may use independently chosen base points in the singularity comparison. -/
theorem geometricHittingMeasure_transport_singularity_at_iff (z w : ℍ) :
    geometricHittingMeasure Λ t ν hν hn hgt hrt w ⟂ₘ compactPoissonMeasure w ↔
      geometricHittingMeasure Γ s μ hμ hm hgs hrs z ⟂ₘ compactPoissonMeasure z :=
  (geometricHittingMeasure_basepoint_singularity_iff Λ t ν hν hn hgt hrt w (B • z)).trans
    (geometricHittingMeasure_transport_singularity_iff Γ Λ s t e μ ν hμ hν hm hn
      hgs hgt hrs hrt hw φ he B ha z)

end Singularity
