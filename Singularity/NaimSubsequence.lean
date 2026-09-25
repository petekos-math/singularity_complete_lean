import Singularity.ReflectedMartin
import Singularity.OrbitGreenBoundary

/-!
# Canonical Green normalizers and a subsequential Naïm-type pairing

This module uses the actual denominators G(x,o)G(o,y), proves their positivity,
and extracts a common subsequence instead of assuming coordinate limits.
Exponential bounds and finite-path separation remain explicit hypotheses.

This is a subsequential limit theorem. It does not prove uniqueness, dependence
only on geometric boundary endpoints, or existence of the full Naïm limit.
-/

noncomputable section
open Filter
open scoped Topology

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The finite Green quotient whose off-diagonal boundary limit is sought. -/
def finiteNaimQuotient (s : Finset Γ) (μ : Γ → ℝ) (o x y : Γ) : ℝ :=
  walkGreen s μ x y / (walkGreen s μ x o * walkGreen s μ o y)

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]

/-- The canonical product normalizer is strictly positive. -/
theorem naim_normalizer_pos (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (o x y : Γ) :
    0 < walkGreen s μ x o * walkGreen s μ o y :=
  mul_pos (walkGreen_pos s μ hpos hgen hgap x o) (walkGreen_pos s μ hpos hgen hgap o y)

/-- The finite quotient is positive, with no convention involving division by zero. -/
theorem finiteNaimQuotient_pos (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (o x y : Γ) :
    0 < finiteNaimQuotient s μ o x y :=
  div_pos (walkGreen_pos s μ hpos hgen hgap x y)
    (naim_normalizer_pos s μ hpos hgen hgap o x y)

variable [Countable Γ] {J : Type*}
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  {A : Set Γ} (e : (ℤ × J) ≃ A)

include hgap in
/-- Canonically normalized Green rows are reflected Martin quotients. -/
theorem orbitGreenRow_martin (o x : Γ) (p : ℤ × J) :
    orbitGreenRow s μ e x (walkGreen s μ x o) p = (reverseMartinQuotient s μ o (e p) x : ℂ) := by
  rw [orbitGreenRow_apply s μ hgap]
  simp only [reverseMartinQuotient, Complex.ofReal_div]

include hgap in
/-- Canonically normalized Green columns are forward Martin quotients. -/
theorem orbitGreenColumn_martin (o y : Γ) (p : ℤ × J) :
    orbitGreenColumn s μ e y (walkGreen s μ o y) p = (martinQuotient s μ o (e p) y : ℂ) := by
  rw [orbitGreenColumn_apply s μ hgap]
  simp only [martinQuotient, Complex.ofReal_div]

/-- The finite Naïm-type quotient equals the actual compressed-inverse pairing. -/
theorem finiteNaim_separator_pairing (o x y : Γ) (hsep : SeparatesJumpPaths s A x y) :
    (finiteNaimQuotient s μ o x y : ℂ) = inner ℂ
      (orbitGreenRow s μ e x (walkGreen s μ x o))
      (orbitGreenInverse s μ hμ hmass hgap e
        (orbitGreenColumn s μ e y (walkGreen s μ o y))) := by
  simpa only [finiteNaimQuotient, Complex.ofReal_div, Complex.ofReal_mul] using
    orbitGreen_separator_pairing s μ hμ hmass hgap e x y
      (walkGreen s μ x o) (walkGreen s μ o y) hsep

/-- Exponential orbit bounds and separation yield a convergent subsequence of the
canonical quotient, with its limit represented by the actual Green pairing.
Coordinate convergence is a conclusion obtained by Martin compactness. -/
theorem finiteNaim_pairing_subsequence [Fintype J]
    (hpos : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (o : Γ) (x y : ℕ → Γ) {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (C D : J → ℝ)
    (hsep : ∀ᶠ n in atTop, SeparatesJumpPaths s A (x n) (y n))
    (hu : ∀ᶠ n in atTop, ∀ p : ℤ × J,
      ‖(reverseMartinQuotient s μ o (e p) (x n) : ℂ)‖ ≤ C p.2 * Real.exp (-τ * |(p.1 : ℝ)|))
    (hv : ∀ᶠ n in atTop, ∀ p : ℤ × J,
      ‖(martinQuotient s μ o (e p) (y n) : ℂ)‖ ≤ D p.2 * Real.exp (-σ * |(p.1 : ℝ)|)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u v : SequenceL2 (ℤ × J),
      Tendsto (fun n => orbitGreenRow s μ e (x (φ n)) (walkGreen s μ (x (φ n)) o)) atTop (𝓝 u) ∧
      Tendsto (fun n => orbitGreenColumn s μ e (y (φ n)) (walkGreen s μ o (y (φ n)))) atTop (𝓝 v) ∧
      Tendsto (fun n => (finiteNaimQuotient s μ o (x (φ n)) (y (φ n)) : ℂ)) atTop
        (𝓝 (inner ℂ u (orbitGreenInverse s μ hμ hmass hgap e v))) := by
  obtain ⟨Hm, Hp, _, _, _, _, φ, hφ, hmt, hpt⟩ :=
    martinPair_subsequence s μ hpos hgen hgap o x y
  have hup : ∀ p : ℤ × J, Tendsto (fun n =>
      (walkGreen s μ (x (φ n)) (e p) : ℂ) / (walkGreen s μ (x (φ n)) o : ℂ)) atTop
      (𝓝 (Hm (e p) : ℂ)) := by
    intro p
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (hmt (e p))
    simpa only [Function.comp_def, reverseMartinQuotient, Complex.ofReal_div] using h
  have hvp : ∀ p : ℤ × J, Tendsto (fun n =>
      (walkGreen s μ (e p) (y (φ n)) : ℂ) / (walkGreen s μ o (y (φ n)) : ℂ)) atTop
      (𝓝 (Hp (e p) : ℂ)) := by
    intro p
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (hpt (e p))
    simpa only [Function.comp_def, martinQuotient, Complex.ofReal_div] using h
  have hu' : ∀ᶠ n in atTop, ∀ p : ℤ × J,
      ‖(walkGreen s μ (x (φ n)) (e p) : ℂ) / (walkGreen s μ (x (φ n)) o : ℂ)‖ ≤
        C p.2 * Real.exp (-τ * |(p.1 : ℝ)|) := by
    simpa only [reverseMartinQuotient, Complex.ofReal_div] using hφ.tendsto_atTop.eventually hu
  have hv' : ∀ᶠ n in atTop, ∀ p : ℤ × J,
      ‖(walkGreen s μ (e p) (y (φ n)) : ℂ) / (walkGreen s μ o (y (φ n)) : ℂ)‖ ≤
        D p.2 * Real.exp (-σ * |(p.1 : ℝ)|) := by
    simpa only [martinQuotient, Complex.ofReal_div] using hφ.tendsto_atTop.eventually hv
  obtain ⟨u, v, _, _, hut, hvt, ht⟩ := orbitGreen_boundary_limit s μ hμ hmass hgap e
    (x ∘ φ) (y ∘ φ) (fun n => walkGreen s μ (x (φ n)) o) (fun n => walkGreen s μ o (y (φ n)))
    (fun p => (Hm (e p) : ℂ)) (fun p => (Hp (e p) : ℂ)) hτ hσ C D
    (hφ.tendsto_atTop.eventually hsep) hu' hv' hup hvp
  refine ⟨φ, hφ, u, v, hut, hvt, ?_⟩
  simpa only [Function.comp_def, finiteNaimQuotient, Complex.ofReal_div, Complex.ofReal_mul] using ht

end Singularity
