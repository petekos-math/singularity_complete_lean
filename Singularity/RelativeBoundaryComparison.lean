import Singularity.RelativeExitFlux
import Singularity.HarmonicEntranceComparison

/-!
# From relative Green bounds to boundary comparison

Only Green values on the additional stopping set enter the last-exit flux.
Two-sided comparison on that set therefore transfers to entrance probabilities
when the direct term vanishes, and then to nonnegative L² harmonic data.
The geometric comparison and separator hypotheses remain explicit.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (A B : Set Γ)

include hμ hmass hgap in
/-- Comparison is needed only on B outside A: the other terms vanish. -/
theorem relativeExitFlux_comparison (x o a : Γ) (L U : ℝ)
    (hcompare : ∀ b ∈ B \ A, L * killedGreen s μ A o b ≤ killedGreen s μ A x b ∧
      killedGreen s μ A x b ≤ U * killedGreen s μ A o b) :
    L * (∑' b : Γ, killedGreen s μ A o b * boundaryExitFlux s μ (A ∪ B) a b) ≤
      (∑' b : Γ, killedGreen s μ A x b * boundaryExitFlux s μ (A ∪ B) a b) ∧
    (∑' b : Γ, killedGreen s μ A x b * boundaryExitFlux s μ (A ∪ B) a b) ≤
      U * (∑' b : Γ, killedGreen s μ A o b * boundaryExitFlux s μ (A ∪ B) a b) := by
  have hsx := relativeExitFlux_summable s μ hμ hmass hgap A B x a
  have hso := relativeExitFlux_summable s μ hμ hmass hgap A B o a
  have ht (b : Γ) :
      L * (killedGreen s μ A o b * boundaryExitFlux s μ (A ∪ B) a b) ≤
        killedGreen s μ A x b * boundaryExitFlux s μ (A ∪ B) a b ∧
      killedGreen s μ A x b * boundaryExitFlux s μ (A ∪ B) a b ≤
        U * (killedGreen s μ A o b * boundaryExitFlux s μ (A ∪ B) a b) := by
    by_cases hbA : b ∈ A
    · simp only [killedGreen_target_mem s μ A _ b hbA, zero_mul, mul_zero, le_refl, and_self]
    by_cases hbB : b ∈ B
    · have hc := hcompare b ⟨hbB, hbA⟩
      have hn := boundaryExitFlux_nonneg s μ hμ (A ∪ B) a b
      exact ⟨by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc.1 hn,
        by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc.2 hn⟩
    · have hb : b ∉ A ∪ B := fun h => h.elim hbA hbB
      simp only [boundaryExitFlux_eq_zero_of_notMem s μ (A ∪ B) a b hb,
        mul_zero, le_refl, and_self]
  constructor
  · rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun b => (ht b).1) (hso.mul_left L) hsx
  · rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun b => (ht b).2) hsx (hso.mul_left U)

include hμ hmass hgap in
/-- When the additional set intercepts every direct entrance, relative Green
comparison gives the same bounds for the original first-entrance rows. -/
theorem firstEntrance_comparison_of_relativeGreen {a : Γ} (ha : a ∈ A)
    (x o : Γ) (L U : ℝ)
    (hx : firstEntranceKernel s μ (A ∪ B) x a = 0)
    (ho : firstEntranceKernel s μ (A ∪ B) o a = 0)
    (hcompare : ∀ b ∈ B \ A, L * killedGreen s μ A o b ≤ killedGreen s μ A x b ∧
      killedGreen s μ A x b ≤ U * killedGreen s μ A o b) :
    L * firstEntranceKernel s μ A o a ≤ firstEntranceKernel s μ A x a ∧
      firstEntranceKernel s μ A x a ≤ U * firstEntranceKernel s μ A o a := by
  rw [firstEntranceKernel_relative_last_exit s μ hμ hmass hgap A B ha x,
    firstEntranceKernel_relative_last_exit s μ hμ hmass hgap A B ha o,
    hx, ho, zero_add, zero_add]
  exact relativeExitFlux_comparison s μ hμ hmass hgap A B x o a L U hcompare

include hμ hmass hgap in
/-- A concrete path-separation condition at every predecessor kills the direct
entrance term. The time-zero exception is excluded explicitly. -/
theorem firstEntrance_eq_zero_of_predecessor_separators {a : Γ} (ha : a ∈ A)
    (x : Γ) (hxa : x ≠ a)
    (hsep : ∀ g ∈ s, SeparatesJumpPaths s A x (a * g⁻¹)) :
    firstEntranceKernel s μ A x a = 0 := by
  rw [firstEntranceKernel_final_jump s μ hμ hmass hgap A ha x, ite_eq_right hxa, zero_add]
  apply Finset.sum_eq_zero
  intro g hg
  rw [killedGreen_eq_zero_of_separator s μ A x (a * g⁻¹) (hsep g hg), mul_zero]

include hμ hmass hgap in
/-- Last-exit Green comparison implies boundary Harnack bounds for every real
L² harmonic function whose boundary data are nonnegative. -/
theorem harmonic_comparison_of_relativeGreen (f : Γ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) 2 Measure.count)
    (hharm : ∀ x, x ∉ A → f x = ∑ g ∈ s, μ g * f (x*g))
    (hboundary : ∀ a ∈ A, 0 ≤ f a) (x o : Γ) (L U : ℝ)
    (hsep : ∀ a ∈ A, firstEntranceKernel s μ (A ∪ B) x a = 0 ∧
      firstEntranceKernel s μ (A ∪ B) o a = 0)
    (hcompare : ∀ b ∈ B \ A, L * killedGreen s μ A o b ≤ killedGreen s μ A x b ∧
      killedGreen s μ A x b ≤ U * killedGreen s μ A o b) :
    L * f o ≤ f x ∧ f x ≤ U * f o := by
  apply harmonic_comparison_of_entrance_comparison s μ hμ hmass hgap A f hf hharm hboundary x o L U
  intro a ha
  exact firstEntrance_comparison_of_relativeGreen s μ hμ hmass hgap A B ha x o L U
    (hsep a ha).1 (hsep a ha).2 hcompare

end Singularity
