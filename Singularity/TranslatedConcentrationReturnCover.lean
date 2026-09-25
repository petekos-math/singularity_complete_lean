import Singularity.VanishingErrorReturnCover

/-!
# Returns from concentration of translated boundary measures

If the inverse mass of the complement of E tends to zero, then the return
error inside every shadow tends to zero. This route needs neither a shadow
cocycle estimate nor differentiation within the shadow sets.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Singularity

/-- Concentration on E controls the return error in an arbitrary shadow family. -/
theorem inverse_shadow_error_of_translated_concentration
    {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
    (ν : Measure B) (g : ℕ → Γ) (S : ℕ → Set B) (E : Set B)
    (hcon : Tendsto (fun n => ν ((fun ξ : B => g n • ξ) ⁻¹' Eᶜ)) atTop (𝓝 0)) :
    Tendsto (fun n => ν ((fun ξ : B => g n • ξ) ⁻¹' (S n \ E))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcon
    (fun _ => bot_le) (fun n => measure_mono ?_)
  exact fun ξ hξ => hξ.2

/-- An eventual corrected shadow cover and concentration of translated
measures give corrected returns to E, with no shadow mass or cocycle inputs. -/
theorem shadow_return_cover_of_translated_concentration
    {Γ B : Type*} [Group Γ] [Countable Γ] [MeasurableSpace B]
    [MulAction Γ B] [MeasurableConstSMul Γ B]
    (ν : Measure B) (hq : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) ν ≪ ν)
    (g : ℕ → Γ) (S : ℕ → Set B) (E : Set B) (F : Finset Γ)
    (hcon : Tendsto (fun n => ν ((fun ξ : B => g n • ξ) ⁻¹' Eᶜ)) atTop (𝓝 0))
    (hcover : ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∀ᶠ n in atTop, g n • (a⁻¹ • ξ) ∈ S n) :
    ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ, g n • (a⁻¹ • ξ) ∈ S n ∩ E := by
  have herr := inverse_shadow_error_of_translated_concentration ν g S E hcon
  have h := finite_corrected_return_cover_of_vanishing_error ν hq
    (fun n => (fun ξ : B => g n • ξ) ⁻¹' S n)
    (fun n => (fun ξ : B => g n • ξ) ⁻¹' E) F
    (by simpa only [preimage_sdiff] using herr) hcover
  filter_upwards [h] with ξ hξ
  obtain ⟨a, ha, n, hn⟩ := hξ
  exact ⟨a, ha, n, hn.1, hn.2⟩

end Singularity
