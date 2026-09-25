import Singularity.ShadowReturnConcentration
import Singularity.VanishingErrorReturnCover
import Singularity.ShrinkingExceptionalSets
import Singularity.AdjustableExceptionalCover

/-!
# Constructing return covers from shadow concentration

Relative concentration in shadows gives vanishing inverse error. Shrinking
inverse-shadow complements and orbit escape give a finite eventual cover.
Together these yield a finite corrected cover by returns to the chosen set.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Singularity

/-- A finite eventual inverse-shadow cover and relative concentration produce
a finite corrected cover by actual returns to E inside the shadows. -/
theorem shadow_return_cover_of_relative_concentration
    {Γ B : Type*} [Group Γ] [Countable Γ] [MeasurableSpace B]
    [MulAction Γ B] [MeasurableConstSMul Γ B]
    (ν : Measure B) [IsFiniteMeasure ν]
    (hq : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) ν ≪ ν)
    (g : ℕ → Γ) (S : ℕ → Set B) {E : Set B}
    (hS : ∀ n, MeasurableSet (S n)) (hE : MeasurableSet E)
    (hpos : ∀ n, 0 < ν (S n)) (D : ℕ → ℝ) (C : ℝ)
    (hbound : ∀ n, ∀ᵐ ξ ∂ν, g n • ξ ∈ S n → |stationaryLogCocycle ν (g n) ξ - D n| ≤ C)
    (hratio : Tendsto (fun n => (ν (S n \ E)).toReal / (ν (S n)).toReal) atTop (𝓝 0))
    (F : Finset Γ)
    (hcover : ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∀ᶠ n in atTop, g n • (a⁻¹ • ξ) ∈ S n) :
    ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ, g n • (a⁻¹ • ξ) ∈ S n ∩ E := by
  have herr := inverse_shadow_error_tendsto_zero ν hq g S hS hE hpos D C hbound hratio
  have h := finite_corrected_return_cover_of_vanishing_error ν hq
    (fun n => (fun ξ : B => g n • ξ) ⁻¹' S n)
    (fun n => (fun ξ : B => g n • ξ) ⁻¹' E) F
    (by simpa only [preimage_sdiff] using herr) hcover
  filter_upwards [h] with ξ hξ
  obtain ⟨a, ha, n, hn⟩ := hξ
  exact ⟨a, ha, n, hn.1, hn.2⟩

/-- Shrinking inverse-shadow complements toward a finite exceptional set,
infinite boundary orbits, and relative shadow concentration construct the
finite return cover. The shrinking and concentration properties are explicit
geometric and differentiation inputs. -/
theorem shadow_return_cover_of_finite_exceptional_set
    {Γ B : Type*} [Group Γ] [Countable Γ] [MeasurableSpace B]
    [TopologicalSpace B] [CompactSpace B] [T1Space B]
    [MulAction Γ B] [MeasurableConstSMul Γ B] [ContinuousConstSMul Γ B]
    (ν : Measure B) [IsFiniteMeasure ν]
    (hq : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) ν ≪ ν)
    (horbit : ∀ ξ : B, (MulAction.orbit Γ ξ).Infinite)
    (g : ℕ → Γ) (S : ℕ → Set B) {E Z : Set B}
    (hS : ∀ n, MeasurableSet (S n)) (hE : MeasurableSet E)
    (hpos : ∀ n, 0 < ν (S n)) (D : ℕ → ℝ) (C : ℝ)
    (hbound : ∀ n, ∀ᵐ ξ ∂ν, g n • ξ ∈ S n → |stationaryLogCocycle ν (g n) ξ - D n| ≤ C)
    (hratio : Tendsto (fun n => (ν (S n \ E)).toReal / (ν (S n)).toReal) atTop (𝓝 0))
    (hZ : Z.Finite)
    (hshrink : ∀ U : Set B, IsOpen U → Z ⊆ U → ∀ᶠ n in atTop,
      ((fun ξ : B => g n • ξ) ⁻¹' S n)ᶜ ⊆ U) :
    ∃ F : Finset Γ, ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ, g n • (a⁻¹ • ξ) ∈ S n ∩ E := by
  obtain ⟨F, hF⟩ := finite_corrected_eventual_cover_of_finite_exceptional_set horbit
    (fun n => (fun ξ : B => g n • ξ) ⁻¹' S n) hZ hshrink
  refine ⟨F, shadow_return_cover_of_relative_concentration ν hq g S hS hE hpos D C hbound hratio F ?_⟩
  exact Filter.Eventually.of_forall hF


/-- The return-cover construction with an adjustable shadow parameter. For
each fixed parameter the cocycle constant and relative-concentration limit
are uniform in n; shrinking toward the exceptional set is required only
after choosing a sufficiently large parameter. -/
theorem shadow_return_cover_of_adjustable_family
    {Γ B I : Type*} [Group Γ] [Countable Γ] [MeasurableSpace B]
    [TopologicalSpace B] [CompactSpace B] [RegularSpace B]
    [MulAction Γ B] [MeasurableConstSMul Γ B] [ContinuousConstSMul Γ B]
    (ν : Measure B) [IsFiniteMeasure ν]
    (hq : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) ν ≪ ν)
    (g : ℕ → Γ) (S : I → ℕ → Set B) {E Z : Set B}
    (hS : ∀ i n, MeasurableSet (S i n)) (hE : MeasurableSet E)
    (hpos : ∀ i n, 0 < ν (S i n)) (D : ℕ → ℝ) (C : I → ℝ)
    (hbound : ∀ i n, ∀ᵐ ξ ∂ν, g n • ξ ∈ S i n →
      |stationaryLogCocycle ν (g n) ξ - D n| ≤ C i)
    (hratio : ∀ i, Tendsto (fun n => (ν (S i n \ E)).toReal / (ν (S i n)).toReal) atTop (𝓝 0))
    (hZ : IsClosed Z) (hescape : ∀ ξ : B, ∃ a : Γ, a⁻¹ • ξ ∉ Z)
    (hshrink : ∀ U : Set B, IsOpen U → Z ⊆ U → ∃ i : I,
      ∀ᶠ n in atTop, ((fun ξ : B => g n • ξ) ⁻¹' S i n)ᶜ ⊆ U) :
    ∃ i : I, ∃ F : Finset Γ, ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ,
      g n • (a⁻¹ • ξ) ∈ S i n ∩ E := by
  obtain ⟨i, F, hF⟩ := finite_eventual_cover_of_adjustable_shadows
    (fun i n => (fun ξ : B => g n • ξ) ⁻¹' S i n) Z hZ hescape hshrink
  refine ⟨i, F, shadow_return_cover_of_relative_concentration ν hq g (S i)
    (hS i) hE (hpos i) D (C i) (hbound i) (hratio i) F ?_⟩
  exact Filter.Eventually.of_forall hF

end Singularity
