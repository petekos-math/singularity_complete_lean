import Singularity.FirstEntrance
import Singularity.StationaryCurrent

/-!
# First-hit bounds for nonnegative harmonic functions and stationary measures

Stopping at a single vertex gives F(x,y) h(y) ≤ h(x) for every nonnegative
superharmonic function. The proof uses finite-time entrance sums and their
proved convergence. Applied to the actual stationary Radon–Nikodym kernels,
it bounds a translated boundary measure by the original family of laws.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical ENNReal

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Finite first-hit sums are bounded by every nonnegative superharmonic function. -/
theorem firstEntrance_partial_superharmonic_bound
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (h : Γ → ℝ) (hp : ∀ x, 0 ≤ h x)
    (hh : ∀ x, ∑ g ∈ s, μ g * h (x * g) ≤ h x) (y : Γ) (N : ℕ) (x : Γ) :
    (∑ n ∈ Finset.range N, firstEntranceWeight s μ {y} n x y) * h y ≤ h x := by
  induction N generalizing x with
  | zero => simpa using hp x
  | succ N ih =>
    rw [Finset.sum_range_succ']
    by_cases hx : x = y
    · subst x
      simp only [firstEntranceWeight_succ_of_mem s μ {y} (mem_singleton y),
        Finset.sum_const_zero, firstEntranceWeight_zero, mem_singleton_iff, and_self,
        ite_true, zero_add, one_mul, le_refl]
    · have hxy : x ∉ ({y} : Set Γ) := hx
      simp_rw [firstEntranceWeight_succ_of_notMem s μ {y} hxy]
      rw [firstEntranceWeight_zero]
      simp only [hx, false_and, ite_false, add_zero]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_mul]
      calc
        _ ≤ ∑ g ∈ s, μ g * h (x * g) := by
          apply Finset.sum_le_sum
          intro g hg
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (ih (x * g)) (hμ g hg)
        _ ≤ h x := hh x

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]

/-- The full first-hit probability satisfies the optional-stopping inequality. -/
theorem firstEntrance_superharmonic_bound
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (h : Γ → ℝ) (hp : ∀ x, 0 ≤ h x)
    (hh : ∀ x, ∑ g ∈ s, μ g * h (x * g) ≤ h x) (x y : Γ) :
    firstEntranceKernel s μ {y} x y * h y ≤ h x := by
  have ht := (firstEntranceWeight_summable s μ hμ hgap {y} x y).hasSum.tendsto_sum_nat.mul_const (h y)
  exact le_of_tendsto ht (Eventually.of_forall
    (fun N => firstEntrance_partial_superharmonic_bound s μ hμ h hp hh y N x))

/-- First-hit probabilities dominate every stationary boundary family of translates. -/
theorem firstEntrance_stationary_measure_domination
    {B : Type*} [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (ν : Measure B) [IsFiniteMeasure ν]
    (hstat : ν = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν)
    (x y : Γ) :
    ENNReal.ofReal (firstEntranceKernel s μ {y} x y) • Measure.map (fun ξ : B => y • ξ) ν ≤
      Measure.map (fun ξ : B => x • ξ) ν := by
  have hh : ∀ᵐ ξ ∂ν,
      firstEntranceKernel s μ {y} x y * stationaryRealDensity ν y ξ ≤ stationaryRealDensity ν x ξ := by
    filter_upwards [stationaryRealDensity_ae_harmonic s μ hpos hgen ν hstat] with ξ hξ
    apply firstEntrance_superharmonic_bound s μ (fun g hg => (hpos g hg).le) hgap
      (fun g => stationaryRealDensity ν g ξ) (fun g => (hξ.2 g).1.le)
      (fun g => by rw [← Finset.sum_coe_sort s]; exact (hξ.2 g).2.ge) x y
  have hf := firstEntranceKernel_nonneg s μ (fun g hg => (hpos g hg).le) {y} x y
  have hm : Measurable (fun ξ => ENNReal.ofReal (stationaryRealDensity ν y ξ)) :=
    (measurable_stationaryDensity ν y).ennreal_toReal.ennreal_ofReal
  rw [← stationaryRealDensity_withDensity s μ hpos hgen ν hstat y,
    ← stationaryRealDensity_withDensity s μ hpos hgen ν hstat x,
    ← withDensity_smul _ hm]
  apply withDensity_mono
  filter_upwards [hh] with ξ hξ
  simpa only [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hf] using
    ENNReal.ofReal_le_ofReal hξ

end Singularity
