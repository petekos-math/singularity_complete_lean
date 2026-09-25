import Singularity.AnalysisOperator
import Singularity.ExponentialLattice
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Bounded analysis by finitely many lattice-translate families

This constructs H from the base profiles themselves. The output coordinates are
indexed by ℤ × J, where J is finite, exactly as in the strip decomposition.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Singularity

variable {J : Type*} [Fintype J]

/-- Finite collections of exponentially decaying profiles have uniformly
bounded overlap under translations by a fixed positive lattice spacing. -/
theorem translated_profiles_overlap {τ : ℝ} (hτ : 0 < τ)
    (k : J → ℝ → ℝ) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hk : ∀ j t, 0 ≤ k j t)
    (hdecay : ∀ j t, k j t ≤ C j * Real.exp (-|t|))
    (s : Finset (ℤ × J)) (t : ℝ) :
    ∑ p ∈ s, k p.2 (t - (p.1 : ℝ) * τ) ≤
      (∑ j, C j) * latticeEnvelopeBound τ := by
  classical
  let ns : Finset ℤ := s.image Prod.fst
  have hs : s ⊆ ns ×ˢ (Finset.univ : Finset J) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst hp, Finset.mem_univ _⟩
  calc
    ∑ p ∈ s, k p.2 (t - (p.1 : ℝ) * τ) ≤
        ∑ p ∈ ns ×ˢ (Finset.univ : Finset J), k p.2 (t - (p.1 : ℝ) * τ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => hk _ _)
    _ ≤ ∑ p ∈ ns ×ˢ (Finset.univ : Finset J),
        C p.2 * Real.exp (-|t - (p.1 : ℝ) * τ|) :=
      Finset.sum_le_sum (fun p _ => hdecay _ _)
    _ = (∑ j, C j) * ∑ n ∈ ns, Real.exp (-|t - (n : ℝ) * τ|) := by
      rw [Finset.sum_product]
      simp_rw [← Finset.sum_mul]
      rw [Finset.mul_sum]
    _ ≤ (∑ j, C j) * latticeEnvelopeBound τ :=
      mul_le_mul_of_nonneg_left (sum_exp_lattice_le hτ t ns)
        (Finset.sum_nonneg (fun j _ => hC j))

/-- Build the family of translated row densities from finitely many
integrable, nonnegative, exponentially decaying base profiles. -/
def translatedDensityFamily {τ : ℝ} (hτ : 0 < τ)
    (k : J → ℝ → ℝ) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hk : ∀ j t, 0 ≤ k j t)
    (hint : ∀ j, Integrable (k j))
    (hmass : ∀ j, ∫ t, k j t ≤ 1)
    (hdecay : ∀ j t, k j t ≤ C j * Real.exp (-|t|)) :
    DensityFamily ℝ (ℤ × J) volume where
  density p t := k p.2 (t - (p.1 : ℝ) * τ)
  nonneg p t := hk _ _
  integrable p := (measurePreserving_sub_right volume ((p.1 : ℝ) * τ)).integrable_comp
    (hint p.2).aestronglyMeasurable |>.mpr (hint p.2)
  mass_le_one p := by
    rw [integral_sub_right_eq_self]
    exact hmass p.2
  overlapBound := (∑ j, C j) * latticeEnvelopeBound τ
  overlapBound_nonneg := mul_nonneg (Finset.sum_nonneg (fun j _ => hC j))
    (latticeEnvelopeBound_nonneg τ)
  overlap s t := translated_profiles_overlap hτ k C hC hk hdecay s t

/-- The resulting H has exactly the lattice-analysis coordinates, with
no boundedness or ℓ²-output hypothesis left to assume. -/
theorem translated_analysis_apply {τ : ℝ} (hτ : 0 < τ)
    (k : J → ℝ → ℝ) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hk : ∀ j t, 0 ≤ k j t)
    (hint : ∀ j, Integrable (k j))
    (hmass : ∀ j, ∫ t, k j t ≤ 1)
    (hdecay : ∀ j t, k j t ≤ C j * Real.exp (-|t|))
    (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℤ) (j : J) :
    (translatedDensityFamily hτ k C hC hk hint hmass hdecay).analysis f (n, j) =
      ∫ t, (k j (t - (n : ℝ) * τ) : ℂ) * f t :=
  DensityFamily.analysis_apply _ _ _

/-- The corresponding bound is uniform over all inputs. -/
theorem translated_analysis_norm_le {τ : ℝ} (hτ : 0 < τ)
    (k : J → ℝ → ℝ) (C : J → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hk : ∀ j t, 0 ≤ k j t)
    (hint : ∀ j, Integrable (k j))
    (hmass : ∀ j, ∫ t, k j t ≤ 1)
    (hdecay : ∀ j t, k j t ≤ C j * Real.exp (-|t|)) :
    ‖(translatedDensityFamily hτ k C hC hk hint hmass hdecay).analysis‖ ≤
      Real.sqrt ((∑ j, C j) * latticeEnvelopeBound τ) :=
  DensityFamily.analysis_norm_le _

end Singularity
