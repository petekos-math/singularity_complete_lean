import Singularity.MartinCompactness

/-!
# Reflected Martin quotients and simultaneous subsequences

The row normalizer G(x,o) belongs to the reflected walk. We transfer the proved
compactness result using the actual transposed Green kernel and the proved
reflection of semigroup generation, then extract a common row/column subsequence.
-/

noncomputable section
open Filter
open scoped Topology

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The row quotient is the Martin quotient for the reflected law. -/
def reverseMartinQuotient (s : Finset Γ) (μ : Γ → ℝ) (o z x : Γ) : ℝ :=
  walkGreen s μ x z / walkGreen s μ x o

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hgap in
/-- Reflection identifies the forward row quotient with an actual Martin quotient. -/
theorem reverseMartinQuotient_eq_reflected (o z x : Γ) :
    reverseMartinQuotient s μ o z x =
      martinQuotient (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) o z x := by
  simp only [reverseMartinQuotient, martinQuotient, reflected_walkGreen s μ hgap]

include hpos hgen hgap in
/-- Forward Green row quotients admit positive normalized pointwise subsequential limits. -/
theorem reverseMartinQuotient_subsequence (o : Γ) (x : ℕ → Γ) :
    ∃ H : Γ → ℝ, H o = 1 ∧ (∀ z, 0 < H z) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ z, Tendsto (fun n => reverseMartinQuotient s μ o z (x (φ n))) atTop (𝓝 (H z)) := by
  have h := martinQuotient_subsequence (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
    (reflectedMarkov_spectral_gap s μ hgap) o x
  simpa only [← reverseMartinQuotient_eq_reflected s μ hgap] using h

include hgap in
/-- Escaping row poles produce a reflected-harmonic limit, with right inverse jumps. -/
theorem reverseMartin_limit_harmonic {α : Type*} {l : Filter α} [l.NeBot]
    (o : Γ) (x : α → Γ) (H : Γ → ℝ)
    (hescape : ∀ z, ∀ᶠ n in l, z ≠ x n)
    (hpoint : ∀ z, Tendsto (fun n => reverseMartinQuotient s μ o z (x n)) l (𝓝 (H z))) (z : Γ) :
    H z = ∑ g ∈ s, μ g * H (z * g⁻¹) := by
  have hp : ∀ z, Tendsto (fun n =>
      martinQuotient (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) o z (x n)) l (𝓝 (H z)) := by
    simpa only [← reverseMartinQuotient_eq_reflected s μ hgap] using hpoint
  have h := martin_limit_harmonic (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflectedMarkov_spectral_gap s μ hgap) o x H hescape hp z
  simpa only [Finset.sum_map, Function.Embedding.coeFn_mk, inv_inv] using h

include hpos hgen hgap in
/-- A single subsequence works for both normalized rows and normalized columns. -/
theorem martinPair_subsequence (o : Γ) (x y : ℕ → Γ) :
    ∃ Hminus Hplus : Γ → ℝ,
      Hminus o = 1 ∧ Hplus o = 1 ∧ (∀ z, 0 < Hminus z) ∧ (∀ z, 0 < Hplus z) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ z, Tendsto (fun n => reverseMartinQuotient s μ o z (x (φ n))) atTop (𝓝 (Hminus z))) ∧
        (∀ z, Tendsto (fun n => martinQuotient s μ o z (y (φ n))) atTop (𝓝 (Hplus z))) := by
  obtain ⟨Hm, hmo, hmp, ψ, hψ, hmt⟩ := reverseMartinQuotient_subsequence s μ hpos hgen hgap o x
  obtain ⟨Hp, hpo, hpp, χ, hχ, hpt⟩ := martinQuotient_subsequence s μ hpos hgen hgap o (y ∘ ψ)
  refine ⟨Hm, Hp, hmo, hpo, hmp, hpp, ψ ∘ χ, hψ.comp hχ, ?_, hpt⟩
  intro z
  exact (hmt z).comp hχ.tendsto_atTop

include hpos hgen hgap in
/-- If both pole sequences escape, their common subsequential limits satisfy the
forward and reflected harmonic equations. -/
theorem exists_harmonic_martinPair (o : Γ) (x y : ℕ → Γ)
    (hx : ∀ z, ∀ᶠ n in atTop, z ≠ x n) (hy : ∀ z, ∀ᶠ n in atTop, z ≠ y n) :
    ∃ Hminus Hplus : Γ → ℝ,
      Hminus o = 1 ∧ Hplus o = 1 ∧ (∀ z, 0 < Hminus z) ∧ (∀ z, 0 < Hplus z) ∧
      (∀ z, Hminus z = ∑ g ∈ s, μ g * Hminus (z * g⁻¹)) ∧
      (∀ z, Hplus z = ∑ g ∈ s, μ g * Hplus (z * g)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ z, Tendsto (fun n => reverseMartinQuotient s μ o z (x (φ n))) atTop (𝓝 (Hminus z))) ∧
        (∀ z, Tendsto (fun n => martinQuotient s μ o z (y (φ n))) atTop (𝓝 (Hplus z))) := by
  obtain ⟨Hm, Hp, hmo, hpo, hmp, hpp, φ, hφ, hmt, hpt⟩ :=
    martinPair_subsequence s μ hpos hgen hgap o x y
  refine ⟨Hm, Hp, hmo, hpo, hmp, hpp, ?_, ?_, φ, hφ, hmt, hpt⟩
  · exact reverseMartin_limit_harmonic s μ hgap o (x ∘ φ) Hm
      (fun z => hφ.tendsto_atTop.eventually (hx z)) hmt
  · exact martin_limit_harmonic s μ hgap o (y ∘ φ) Hp
      (fun z => hφ.tendsto_atTop.eventually (hy z)) hpt

end Singularity
