import Singularity.InfiniteWalkLaw
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The infinite random-walk process and its Green occupation law

The position variables are actual measurable functions on the product path
space. Their time-n laws agree with the finite endpoint laws. The Green sum
is the expected number of visits, and the spectral gap implies almost-sure
escape from every finite set for a countable group.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The position after the first n jumps of an infinite sample. -/
def walkPosition (s : Finset Γ) (x : Γ) (n : ℕ) (ω : ℕ → s) : Γ :=
  walkEndpoint s n x (walkPrefix s n ω)

theorem walkPosition_zero (s : Finset Γ) (x : Γ) (ω : ℕ → s) : walkPosition s x 0 ω = x := rfl

/-- First-step recursion for the actual infinite-path process. -/
theorem walkPosition_succ (s : Finset Γ) (x : Γ) (n : ℕ) (ω : ℕ → s) :
    walkPosition s x (n + 1) ω = walkPosition s (x * ω 0) n (fun k => ω (k + 1)) := rfl

/-- Moving the initial point translates the entire sample path on the left. -/
theorem walkPosition_left (s : Finset Γ) (z x : Γ) (n : ℕ) (ω : ℕ → s) :
    walkPosition s (z * x) n ω = z * walkPosition s x n ω :=
  walkEndpoint_left s n z x _

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- All time evaluations are measurable random variables. -/
theorem measurable_walkPosition (s : Finset Γ) (x : Γ) (n : ℕ) :
    Measurable (walkPosition s x n) :=
  (measurable_of_countable (walkEndpoint s n x)).comp (measurable_walkPrefix s n)

/-- Visiting a prescribed vertex at a prescribed time is a measurable event. -/
theorem measurableSet_walkPosition (s : Finset Γ) (x y : Γ) (n : ℕ) :
    MeasurableSet {ω : ℕ → s | walkPosition s x n ω = y} :=
  (measurableSet_singleton y).preimage (measurable_walkPosition s x n)

/-- The time-n law of the infinite walk is exactly the finite endpoint law. -/
theorem walkPosition_law (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (x : Γ) (n : ℕ) :
    Measure.map (walkPosition s x n) (infiniteWalkLaw s μ hμ hmass) =
      (finiteEndpointLaw s μ hμ hmass n x).toMeasure := by
  change Measure.map ((walkEndpoint s n x) ∘ walkPrefix s n) _ = _
  rw [← Measure.map_map (measurable_of_countable _) (measurable_walkPrefix s n),
    infiniteWalkLaw_prefix, PMF.toMeasure_map _ _ (measurable_of_countable _)]
  rfl

/-- Transition weights are probabilities on the single infinite path space. -/
theorem walkPosition_probability (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (x y : Γ) (n : ℕ) :
    infiniteWalkLaw s μ hμ hmass {ω | walkPosition s x n ω = y} =
      ENNReal.ofReal (transitionWeight s μ n x y) := by
  change infiniteWalkLaw s μ hμ hmass ((walkPosition s x n) ⁻¹' {y}) = _
  rw [← Measure.map_apply (measurable_walkPosition s x n) (measurableSet_singleton y),
    walkPosition_law, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y),
    finiteEndpointLaw_apply]

/-- Extended number of visits to y, including time zero. -/
def walkVisitCount (s : Finset Γ) (x y : Γ) (ω : ℕ → s) : ℝ≥0∞ :=
  ∑' n : ℕ, {ω | walkPosition s x n ω = y}.indicator (fun _ => 1) ω

theorem measurable_walkVisitCount (s : Finset Γ) (x y : Γ) :
    Measurable (walkVisitCount s x y) := by
  apply Measurable.tsum
  intro n
  exact measurable_const.indicator (measurableSet_walkPosition s x y n)

/-- Tonelli identifies expected visits with the sum of time-n probabilities. -/
theorem lintegral_walkVisitCount (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (x y : Γ) :
    ∫⁻ ω, walkVisitCount s x y ω ∂infiniteWalkLaw s μ hμ hmass =
      ∑' n : ℕ, ENNReal.ofReal (transitionWeight s μ n x y) := by
  unfold walkVisitCount
  rw [lintegral_tsum (fun n =>
    (measurable_const.indicator (measurableSet_walkPosition s x y n)).aemeasurable)]
  apply tsum_congr
  intro n
  change (∫⁻ ω, {ω | walkPosition s x n ω = y}.indicator 1 ω ∂infiniteWalkLaw s μ hμ hmass) = _
  rw [lintegral_indicator_one (measurableSet_walkPosition s x y n)]
  exact walkPosition_probability s μ hμ hmass x y n

variable [MeasurableMul Γ]

/-- The Green kernel is the expected number of visits of the actual infinite walk. -/
theorem walkGreen_eq_expected_visits (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    ∫⁻ ω, walkVisitCount s x y ω ∂infiniteWalkLaw s μ hμ hmass =
      ENNReal.ofReal (walkGreen s μ x y) := by
  rw [lintegral_walkVisitCount, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => transitionWeight_nonneg s μ hμ n x y) (walkGreen_summable s μ hgap x y)]
  rfl

/-- The total number of visits to each prescribed vertex is almost surely finite. -/
theorem walkVisitCount_ae_lt_top (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass, walkVisitCount s x y ω < ∞ := by
  apply ae_lt_top (measurable_walkVisitCount s x y)
  rw [walkGreen_eq_expected_visits s μ hμ hmass hgap]
  exact ENNReal.ofReal_ne_top

/-- Almost surely the path eventually stops visiting any given group vertex. -/
theorem walkPosition_ae_eventually_ne (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass, ∀ᶠ n in atTop, walkPosition s x n ω ≠ y := by
  apply ae_eventually_notMem (s := fun n => {ω | walkPosition s x n ω = y})
  simp only [walkPosition_probability s μ hμ hmass]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => transitionWeight_nonneg s μ hμ n x y)
    (walkGreen_summable s μ hgap x y)]
  exact ENNReal.ofReal_ne_top

/-- Countability puts escape from every vertex on one common full-measure set. -/
theorem walkPosition_ae_transient [Countable Γ] (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass, ∀ y : Γ, ∀ᶠ n in atTop, walkPosition s x n ω ≠ y :=
  ae_all_iff.mpr (fun y => walkPosition_ae_eventually_ne s μ hμ hmass hgap x y)

/-- Almost every path eventually leaves every finite subset of the group. -/
theorem walkPosition_ae_escape_finite [Countable Γ] (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass, ∀ K : Finset Γ,
      ∀ᶠ n in atTop, walkPosition s x n ω ∉ K := by
  filter_upwards [walkPosition_ae_transient s μ hμ hmass hgap x] with ω hω
  intro K
  induction K using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall (fun n => by simp)
  | @insert a K ha ih =>
    filter_upwards [hω a, ih] with n hn hk
    simpa only [Finset.mem_insert, not_or] using And.intro hn hk

end Singularity
