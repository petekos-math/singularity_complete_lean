import Singularity.HittingConjugacy
import Singularity.GeometricKernelCurrent

/-!
# Transport of reflected hitting laws

Inverting each support label on both sides of a walk relabeling transports the
reflected law. The group homomorphism commutes with inversion, so the same
hyperbolic coordinate change applies to both hitting measures.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- Inversion is a bijection from the jump alphabet to the reflected alphabet. -/
def invertedSupportEquiv {Γ : Type*} [Group Γ] (s : Finset Γ) :
    s ≃ s.map ⟨Inv.inv, inv_injective⟩ where
  toFun g := ⟨(g : Γ)⁻¹, Finset.mem_map.mpr ⟨g, g.property, rfl⟩⟩
  invFun g := ⟨(g : Γ)⁻¹, by
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp g.property
    change a⁻¹ = (g : Γ) at he
    rw [← he, inv_inv]
    exact ha⟩
  left_inv g := by apply Subtype.ext; exact inv_inv (g : Γ)
  right_inv g := by apply Subtype.ext; exact inv_inv (g : Γ)

/-- Reflect a relabeling of two finite jump alphabets. -/
def reflectedSupportEquiv {Γ Λ : Type*} [Group Γ] [Group Λ]
    (s : Finset Γ) (t : Finset Λ) (e : s ≃ t) :
    s.map ⟨Inv.inv, inv_injective⟩ ≃ t.map ⟨Inv.inv, inv_injective⟩ :=
  (invertedSupportEquiv s).symm.trans (e.trans (invertedSupportEquiv t))

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

include hw he ha in
/-- Coordinate changes preserve and reflect singularity of the reflected hitting laws too. -/
theorem reflectedGeometricHittingMeasure_transport_singularity_iff (z : ℍ) :
    reflectedGeometricHittingMeasure Λ t ν hν hn hgt hrt (B • z) ⟂ₘ compactPoissonMeasure (B • z) ↔
      reflectedGeometricHittingMeasure Γ s μ hμ hm hgs hrs z ⟂ₘ compactPoissonMeasure z := by
  have hw' (g : s.map ⟨Inv.inv, inv_injective⟩) :
      ν ((reflectedSupportEquiv s t e g : Λ)⁻¹) = μ (g : Γ)⁻¹ := by
    change ν (((e ((invertedSupportEquiv s).symm g) : t) : Λ)⁻¹)⁻¹ = _
    rw [inv_inv, hw]
    rfl
  have he' (g : s.map ⟨Inv.inv, inv_injective⟩) :
      (reflectedSupportEquiv s t e g : Λ) = φ g := by
    change ((e ((invertedSupportEquiv s).symm g) : t) : Λ)⁻¹ = _
    rw [he]
    change (φ ((g : Γ)⁻¹))⁻¹ = φ g
    rw [map_inv, inv_inv]
  exact geometricHittingMeasure_transport_singularity_iff Γ Λ
    (s.map ⟨Inv.inv, inv_injective⟩) (t.map ⟨Inv.inv, inv_injective⟩) (reflectedSupportEquiv s t e)
    (fun g => μ g⁻¹) (fun g => ν g⁻¹) (reflected_jump_pos s μ hμ) (reflected_jump_pos t ν hν)
    ((reflected_jump_mass s μ).trans hm) ((reflected_jump_mass t ν).trans hn)
    (reflected_support_generates s hgs) (reflected_support_generates t hgt)
    (reflectedMarkov_spectral_gap s μ hrs) (reflectedMarkov_spectral_gap t ν hrt)
    hw' φ he' B ha z

end Singularity
