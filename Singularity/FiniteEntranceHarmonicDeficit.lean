import Singularity.StationaryLogCocycle
import Singularity.FiniteEntranceDecomposition

/-!
# A finite entrance representation bounds the Green deficit

For every fixed finite entrance set, normalized positive harmonic functions
satisfying an entrance upper representation have a uniform Green comparison.
The constant does not depend on the function or the starting point. Applied
to actual stationary densities, this gives local cocycle deficit bounds.
The entrance representation on the chosen boundary region remains an input;
no L² hypothesis on the boundary harmonic functions is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hmass hgen hgap

/-- Finite entrance averaging gives a uniform Green upper bound for every
normalized positive superharmonic function admitting that representation. -/
theorem finite_entrance_normalized_harmonic_bound (A : Finset Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : Γ → ℝ, (∀ a, 0 < H a) → H 1 = 1 →
      (∀ a, ∑ b ∈ s, μ b * H (a * b) ≤ H a) → ∀ x : Γ,
      H x ≤ ∑ a : A, firstEntranceKernel s μ (A : Set Γ) x a * H a →
        H x ≤ C * walkGreen s μ x 1 := by
  let k : A → ℝ := fun a => walkGreen s μ 1 1 /
    (walkGreen s μ 1 a * walkGreen s μ a 1)
  have hk (a : A) : 0 ≤ k a := by
    exact (div_pos (walkGreen_pos s μ hpos hgen hgap 1 1)
      (mul_pos (walkGreen_pos s μ hpos hgen hgap 1 a)
        (walkGreen_pos s μ hpos hgen hgap a 1))).le
  let C := 1 + ∑ a : A, k a
  have hC : 0 < C := by
    change 0 < 1 + ∑ a : A, k a
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun a _ => hk a))
  refine ⟨C, hC, fun H hp h1 hh x hentrance => ?_⟩
  have hterm (a : A) : H a ≤ C * walkGreen s μ a 1 := by
    have hsuper := walkGreen_superharmonic_bound s μ (fun g hg => (hpos g hg).le)
      hmass hgap H (fun a => (hp a).le) hh 1 a
    rw [walkGreen_diagonal_eq, h1, mul_one] at hsuper
    have ha : 0 < walkGreen s μ 1 a := walkGreen_pos s μ hpos hgen hgap 1 a
    have hb : 0 < walkGreen s μ a 1 := walkGreen_pos s μ hpos hgen hgap a 1
    have hkC : k a ≤ C := by
      have h := Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => hk a)
        (Finset.mem_univ a)
      change k a ≤ 1 + ∑ b : A, k b
      exact h.trans (le_add_of_nonneg_left zero_le_one)
    have hbound := (div_le_iff₀ (mul_pos ha hb)).mp hkC
    have hh' : H a * walkGreen s μ 1 a ≤ (C * walkGreen s μ a 1) * walkGreen s μ 1 a := by
      nlinarith
    exact (mul_le_mul_iff_of_pos_right ha).mp hh'
  calc
    H x ≤ ∑ a : A, firstEntranceKernel s μ (A : Set Γ) x a * H a := hentrance
    _ ≤ ∑ a : A, firstEntranceKernel s μ (A : Set Γ) x a * (C * walkGreen s μ a 1) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hterm a)
        (firstEntranceKernel_nonneg s μ (fun g hg => (hpos g hg).le) _ _ _)
    _ = C * ∑ a : A, firstEntranceKernel s μ (A : Set Γ) x a * walkGreen s μ a 1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ C * walkGreen s μ x 1 := mul_le_mul_of_nonneg_left
      (finite_entrance_green_sum_le s μ (fun g hg => (hpos g hg).le) hmass hgap A x 1) hC.le

/-- On any boundary region admitting a finite entrance upper representation,
the actual stationary cocycle has a Green deficit bounded independently of
the group element and the region. The bound depends only on the entrance set. -/
theorem stationary_deficit_bound_of_finite_entrance
    {B : Type*} [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
    (ν : Measure B) [IsFiniteMeasure ν]
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν)
    (A : Finset Γ) :
    ∃ R : ℝ, ∀ g : Γ, ∀ E : Set B,
      (∀ᵐ ξ ∂ν, ξ ∈ E → stationaryRealDensity ν g⁻¹ ξ ≤
        ∑ a : A, firstEntranceKernel s μ (A : Set Γ) g⁻¹ a * stationaryRealDensity ν (a : Γ) ξ) →
      ∀ᵐ ξ ∂ν, ξ ∈ E → greenDistance s μ 1 g - stationaryLogCocycle ν g ξ ≤ R := by
  obtain ⟨C, hC, hbound⟩ := finite_entrance_normalized_harmonic_bound s μ hpos hmass hgen hgap A
  have hbase : 0 < walkGreen s μ 1 1 := walkGreen_pos s μ hpos hgen hgap 1 1
  refine ⟨Real.log C + Real.log (walkGreen s μ 1 1), fun g E hentrance => ?_⟩
  filter_upwards [stationaryRealDensity_ae_harmonic s μ hpos hgen ν hstat, hentrance]
    with ξ hξ hent hE
  have hb := hbound (fun a => stationaryRealDensity ν a ξ) (fun a => (hξ.2 a).1) hξ.1
    (fun a => by rw [← Finset.sum_coe_sort s]; exact (hξ.2 a).2.symm.le) g⁻¹ (hent hE)
  have hp : 0 < walkGreen s μ g⁻¹ 1 := walkGreen_pos s μ hpos hgen hgap g⁻¹ 1
  have hlog := Real.log_le_log (hξ.2 g⁻¹).1 hb
  rw [Real.log_mul hC.ne' hp.ne'] at hlog
  have hG : walkGreen s μ g⁻¹ 1 = walkGreen s μ 1 g := by
    simpa only [mul_inv_cancel, mul_one] using (walkGreen_left s μ g g⁻¹ 1).symm
  rw [hG] at hlog
  change -Real.log (walkGreen s μ 1 g / walkGreen s μ 1 1) -
    -Real.log (stationaryRealDensity ν g⁻¹ ξ) ≤ _
  rw [Real.log_div (walkGreen_pos s μ hpos hgen hgap 1 g).ne' hbase.ne']
  linarith

end Singularity
