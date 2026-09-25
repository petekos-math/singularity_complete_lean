import Singularity.GreenAdjoint
import Singularity.CountingSequence
import Singularity.GreenSeparator

/-!
# Normalized Green rows, columns, and their boundary pairing

The limit theorem below concerns the actual path Green kernel and compressed
Green inverse. Coordinate limits and square-summable envelopes are explicit
hypotheses; their geometric construction is not supplied by this module.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace Singularity

variable {Γ : Type*} [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- Restriction to the supported subspace is a contraction. -/
theorem supportedRestriction_norm_le (A : Set Γ) (f : GroupL2 Γ) :
    ‖supportedRestriction A f‖ ≤ ‖f‖ := by
  have h : ‖supportedRestriction A‖ ≤ 1 := by
    change ‖(supportedInclusion A).toContinuousLinearMap.adjoint‖ ≤ 1
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (supportedInclusion A).norm_toContinuousLinearMap_le
  exact ((supportedRestriction A).le_opNorm f).trans
    ((mul_le_mul_of_nonneg_right h (norm_nonneg f)).trans_eq (one_mul _))

variable [Group Γ] [MeasurableMul Γ]

/-- The restricted Green row, represented by an adjoint column. -/
def greenRow (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x : Γ) : supportedL2 A :=
  supportedRestriction A ((green (rightMarkov s μ)).adjoint (countingDelta x))

/-- The restricted Green column. -/
def greenColumn (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (y : Γ) : supportedL2 A :=
  supportedRestriction A (green (rightMarkov s μ) (countingDelta y))

theorem greenRow_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (x : Γ) (a : A) :
    (greenRow s μ A x : GroupL2 Γ) a = (walkGreen s μ x a : ℂ) := by
  rw [greenRow, supportedRestriction_apply, green_adjoint_coefficient s μ hgap]

theorem greenColumn_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (y : Γ) (a : A) :
    (greenColumn s μ A y : GroupL2 Γ) a = (walkGreen s μ a y : ℂ) := by
  rw [greenColumn, supportedRestriction_apply, ← walkGreen_eq_coefficient s μ hgap]

theorem greenRow_norm_le (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x : Γ) :
    ‖greenRow s μ A x‖ ≤ ‖green (rightMarkov s μ)‖ := by
  apply (supportedRestriction_norm_le A _).trans
  simpa only [countingDelta_norm, mul_one, ContinuousLinearMap.adjoint.norm_map]
    using (green (rightMarkov s μ)).adjoint.le_opNorm (countingDelta x)

theorem greenColumn_norm_le (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (y : Γ) :
    ‖greenColumn s μ A y‖ ≤ ‖green (rightMarkov s μ)‖ := by
  apply (supportedRestriction_norm_le A _).trans
  simpa only [countingDelta_norm, mul_one]
    using (green (rightMarkov s μ)).le_opNorm (countingDelta y)

/-- Real normalization keeps the row pairing's conjugation consistent. -/
def normalizedGreenRow (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x : Γ) (r : ℝ) :
    supportedL2 A := (r : ℂ)⁻¹ • greenRow s μ A x

def normalizedGreenColumn (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (y : Γ) (c : ℝ) :
    supportedL2 A := (c : ℂ)⁻¹ • greenColumn s μ A y

theorem normalizedGreenRow_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (x : Γ) (r : ℝ) (a : A) :
    (normalizedGreenRow s μ A x r : GroupL2 Γ) a = (walkGreen s μ x a : ℂ) / (r : ℂ) := by
  change ((r : ℂ)⁻¹ • (greenRow s μ A x : GroupL2 Γ)) a = _
  rw [counting_smul_apply, greenRow_apply s μ hgap]
  simp [div_eq_mul_inv, mul_comm]

theorem normalizedGreenColumn_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (y : Γ) (c : ℝ) (a : A) :
    (normalizedGreenColumn s μ A y c : GroupL2 Γ) a = (walkGreen s μ a y : ℂ) / (c : ℂ) := by
  change ((c : ℂ)⁻¹ • (greenColumn s μ A y : GroupL2 Γ)) a = _
  rw [counting_smul_apply, greenColumn_apply s μ hgap]
  simp [div_eq_mul_inv, mul_comm]

variable [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ)

/-- The finite-path separator identity after arbitrary real normalizations. -/
theorem normalizedGreen_separator_pairing (x y : Γ) (r c : ℝ)
    (hsep : SeparatesJumpPaths s A x y) :
    (walkGreen s μ x y : ℂ) / ((r : ℂ) * (c : ℂ)) = inner ℂ
      (normalizedGreenRow s μ A x r)
      ((walkGreenCompression s μ hμ hmass hgap A).symm
        (normalizedGreenColumn s μ A y c)) := by
  rw [normalizedGreenRow, normalizedGreenColumn, map_smul]
  rw [inner_smul_left (𝕜 := ℂ) (E := supportedL2 A),
    inner_smul_right (𝕜 := ℂ) (E := supportedL2 A)]
  simp only [map_inv₀, Complex.conj_ofReal]
  change _ = (r : ℂ)⁻¹ * ((c : ℂ)⁻¹ * inner ℂ
    (supportedRestriction A ((green (rightMarkov s μ)).adjoint (countingDelta x)))
    ((walkGreenCompression s μ hμ hmass hgap A).symm
      (supportedRestriction A (green (rightMarkov s μ) (countingDelta y)))))
  rw [← walkGreen_separator_pairing s μ hμ hmass hgap A x y hsep]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Dominated coordinate limits justify the boundary passage in the actual Green
separator formula. This does not assert the geometric hypotheses hold. -/
theorem normalizedGreen_boundary_limit {α : Type*} {l : Filter α} [l.NeBot]
    (x y : α → Γ) (r c : α → ℝ) (u₀ v₀ : Γ → ℂ) (b d : Γ → ℝ)
    (hsep : ∀ᶠ n in l, SeparatesJumpPaths s A (x n) (y n))
    (hb : Summable (fun a => b a ^ 2)) (hd : Summable (fun a => d a ^ 2))
    (hu : ∀ᶠ n in l, ∀ a, ‖(normalizedGreenRow s μ A (x n) (r n) : GroupL2 Γ) a‖ ≤ b a)
    (hv : ∀ᶠ n in l, ∀ a, ‖(normalizedGreenColumn s μ A (y n) (c n) : GroupL2 Γ) a‖ ≤ d a)
    (hup : ∀ a, Tendsto (fun n => (normalizedGreenRow s μ A (x n) (r n) : GroupL2 Γ) a)
      l (𝓝 (u₀ a)))
    (hvp : ∀ a, Tendsto (fun n => (normalizedGreenColumn s μ A (y n) (c n) : GroupL2 Γ) a)
      l (𝓝 (v₀ a))) :
    ∃ u v : supportedL2 A,
      (∀ a, (u : GroupL2 Γ) a = u₀ a) ∧ (∀ a, (v : GroupL2 Γ) a = v₀ a) ∧
      Tendsto (fun n => (walkGreen s μ (x n) (y n) : ℂ) / ((r n : ℂ) * (c n : ℂ)))
        l (𝓝 (inner ℂ u ((walkGreenCompression s μ hμ hmass hgap A).symm v))) := by
  obtain ⟨u, hueq, hut⟩ := supportedL2_limit_exists A hb hu hup
  obtain ⟨v, hveq, hvt⟩ := supportedL2_limit_exists A hd hv hvp
  refine ⟨u, v, hueq, hveq, ?_⟩
  have ht := pairing_tendsto (walkGreenCompression s μ hμ hmass hgap A).symm.toContinuousLinearMap hut hvt
  apply ht.congr'
  filter_upwards [hsep] with n hn
  exact (normalizedGreen_separator_pairing s μ hμ hmass hgap A (x n) (y n) (r n) (c n) hn).symm

end Singularity
