import Singularity.GreenHarnack
import Singularity.ReflectedSupport
import Mathlib.Topology.Sequences

/-!
# Finite Martin quotients and compactness of normalized Green functions

Strict positivity makes the usual normalizers legitimate. Path Harnack bounds
place every coordinate in a fixed compact interval. For a countable group this
gives subsequential pointwise convergence; an escaping pole makes every such
limit a positive normalized harmonic function.

This is not uniqueness of the limit, nor identification with the geometric
boundary or construction of the off-diagonal Naïm limit.
-/

noncomputable section
open Filter
open scoped Topology Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The finite Martin quotient based at o, with pole y and evaluation point z. -/
def martinQuotient (s : Finset Γ) (μ : Γ → ℝ) (o z y : Γ) : ℝ :=
  walkGreen s μ z y / walkGreen s μ o y

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hgen hgap in
/-- The quotients are strictly positive, with actual nonzero Green denominators. -/
theorem martinQuotient_pos (o z y : Γ) : 0 < martinQuotient s μ o z y :=
  div_pos (walkGreen_pos s μ hpos hgen hgap z y) (walkGreen_pos s μ hpos hgen hgap o y)

include hpos hgen hgap in
/-- The quotient equals one at the basepoint. -/
theorem martinQuotient_base (o y : Γ) : martinQuotient s μ o o y = 1 :=
  div_self (walkGreen_ne_zero s μ hpos hgen hgap o y)

include hpos hgen hgap in
/-- Each coordinate has positive lower and finite upper bounds independent of the pole. -/
theorem martinQuotient_bounds (o z : Γ) :
    ∃ L U : ℝ, 0 < L ∧ ∀ y, L ≤ martinQuotient s μ o z y ∧ martinQuotient s μ o z y ≤ U := by
  obtain ⟨C, hC, hCy⟩ := exists_greenHarnackConstant s μ hgap hpos hgen o z
  obtain ⟨D, hD, hDy⟩ := exists_greenHarnackConstant s μ hgap hpos hgen z o
  refine ⟨D⁻¹, C, inv_pos.mpr hD, ?_⟩
  intro y
  have hden := walkGreen_pos s μ hpos hgen hgap o y
  constructor
  · apply (le_div_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_left (hDy y) (inv_pos.mpr hD).le
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hD), one_mul] using h
  · exact (div_le_iff₀ hden).mpr (hCy y)

include hgap in
/-- Away from its pole, the finite Martin quotient is P-harmonic. -/
theorem martinQuotient_harmonic_off_pole (o z y : Γ) (hzy : z ≠ y) :
    martinQuotient s μ o z y = ∑ g ∈ s, μ g * martinQuotient s μ o (z * g) y := by
  unfold martinQuotient
  rw [walkGreen_first_step s μ hgap z y, ite_eq_right_iff.mpr (fun h => (hzy h).elim), zero_add, Finset.sum_div]
  simp only [mul_div_assoc]

include hpos hgen hgap in
/-- Pointwise limits keep the basepoint normalization. -/
theorem martin_limit_base {α : Type*} {l : Filter α} [l.NeBot]
    (o : Γ) (y : α → Γ) (H : Γ → ℝ)
    (hpoint : ∀ z, Tendsto (fun n => martinQuotient s μ o z (y n)) l (𝓝 (H z))) : H o = 1 := by
  have h := hpoint o
  simp only [martinQuotient_base s μ hpos hgen hgap] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

include hpos hgen hgap in
/-- The lower Harnack bound makes every pointwise limit strictly positive. -/
theorem martin_limit_pos {α : Type*} {l : Filter α} [l.NeBot]
    (o : Γ) (y : α → Γ) (H : Γ → ℝ)
    (hpoint : ∀ z, Tendsto (fun n => martinQuotient s μ o z (y n)) l (𝓝 (H z))) (z : Γ) :
    0 < H z := by
  obtain ⟨L, U, hL, hb⟩ := martinQuotient_bounds s μ hpos hgen hgap o z
  exact hL.trans_le (ge_of_tendsto (hpoint z) (Eventually.of_forall (fun n => (hb (y n)).1)))

include hgap in
/-- When the poles escape each fixed state, the pointwise limit is harmonic. -/
theorem martin_limit_harmonic {α : Type*} {l : Filter α} [l.NeBot]
    (o : Γ) (y : α → Γ) (H : Γ → ℝ)
    (hescape : ∀ z, ∀ᶠ n in l, z ≠ y n)
    (hpoint : ∀ z, Tendsto (fun n => martinQuotient s μ o z (y n)) l (𝓝 (H z))) (z : Γ) :
    H z = ∑ g ∈ s, μ g * H (z * g) := by
  have hs := tendsto_finsetSum s (fun g _ => (hpoint (z * g)).const_mul (μ g))
  have he : (fun n => martinQuotient s μ o z (y n)) =ᶠ[l]
      (fun n => ∑ g ∈ s, μ g * martinQuotient s μ o (z * g) (y n)) := by
    filter_upwards [hescape z] with n hn
    exact martinQuotient_harmonic_off_pole s μ hgap o z (y n) hn
  exact tendsto_nhds_unique ((hpoint z).congr' he) hs

include hpos hgen hgap in
/-- Any sequence of poles has a subsequence whose Martin quotients converge at every state. -/
theorem martinQuotient_subsequence (o : Γ) (y : ℕ → Γ) :
    ∃ H : Γ → ℝ, H o = 1 ∧ (∀ z, 0 < H z) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ z, Tendsto (fun n => martinQuotient s μ o z (y (φ n))) atTop (𝓝 (H z)) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  choose L U hL hb using martinQuotient_bounds s μ hpos hgen hgap o
  have hc : IsCompact {f : Γ → ℝ | ∀ z, f z ∈ Set.Icc (L z) (U z)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hm (n : ℕ) : (fun z => martinQuotient s μ o z (y n)) ∈
      {f : Γ → ℝ | ∀ z, f z ∈ Set.Icc (L z) (U z)} := fun z => hb z (y n)
  obtain ⟨H, hH, φ, hφ, ht⟩ := hc.tendsto_subseq hm
  have hp : ∀ z, Tendsto (fun n => martinQuotient s μ o z (y (φ n))) atTop (𝓝 (H z)) :=
    tendsto_pi_nhds.mp ht
  exact ⟨H, martin_limit_base s μ hpos hgen hgap o (y ∘ φ) H hp,
    fun z => (hL z).trans_le (hH z).1, φ, hφ, hp⟩

include hpos hgen hgap in
/-- Escaping poles yield a positive normalized harmonic subsequential limit. -/
theorem exists_positive_harmonic_martin_limit (o : Γ) (y : ℕ → Γ)
    (hescape : ∀ z, ∀ᶠ n in atTop, z ≠ y n) :
    ∃ H : Γ → ℝ, H o = 1 ∧ (∀ z, 0 < H z) ∧
      (∀ z, H z = ∑ g ∈ s, μ g * H (z * g)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ z, Tendsto (fun n => martinQuotient s μ o z (y (φ n))) atTop (𝓝 (H z)) := by
  obtain ⟨H, ho, hposH, φ, hφ, ht⟩ := martinQuotient_subsequence s μ hpos hgen hgap o y
  refine ⟨H, ho, hposH, ?_, φ, hφ, ht⟩
  exact martin_limit_harmonic s μ hgap o (y ∘ φ) H
    (fun z => hφ.tendsto_atTop.eventually (hescape z)) ht

end Singularity
