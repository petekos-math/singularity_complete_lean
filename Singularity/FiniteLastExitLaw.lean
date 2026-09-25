import Singularity.WalkLastExit
import Singularity.MartinCompactness

/-!
# The finite last-exit law and its exact Martin density

Almost-sure escape makes the last-exit events a partition for a finite set
containing the starting point. This constructs a probability mass function.
Changing the starting vertex multiplies its masses by the actual finite
Martin quotient, without dividing by the possibly zero escape probability.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical
namespace Singularity

/-- A sequence starting in A and eventually avoiding A has a last visit. -/
theorem exists_last_visit_of_eventually_avoid {X : Type*} (f : ℕ → X) (A : Set X)
    (hzero : f 0 ∈ A) (havoid : ∀ᶠ n in atTop, f n ∉ A) :
    ∃ n, f n ∈ A ∧ ∀ k, n < k → f k ∉ A := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 havoid
  have hex : ∃ n, ∀ k, n < k → f k ∉ A := ⟨N, fun k hk => hN k hk.le⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_contra hn
  cases he : Nat.find hex with
  | zero => exact hn (he ▸ hzero)
  | succ m =>
    have hp : ∀ k, m < k → f k ∉ A := by
      intro k hk
      by_cases hkm : k = m + 1
      · subst k
        simpa only [he] using hn
      · exact Nat.find_spec hex k (by omega)
    exact (Nat.find_min hex (show m < Nat.find hex by omega)) hp

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ] [Countable Γ]

/-- Almost every path starting in a finite A has a last exit at a vertex of A. -/
theorem walkLastExitEver_ae_cover (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x : Γ) (hx : x ∈ A) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass, ω ∈ ⋃ a : A, walkLastExitEver s (A : Set Γ) x a := by
  filter_upwards [walkPosition_ae_escape_finite s μ hμ hmass hgap x] with ω hω
  obtain ⟨n, hn, ht⟩ := exists_last_visit_of_eventually_avoid (fun n => walkPosition s x n ω)
    (A : Set Γ) hx (hω A)
  exact mem_iUnion.mpr ⟨⟨walkPosition s x n ω, hn⟩, mem_iUnion.mpr ⟨n, rfl, hn, ht⟩⟩

/-- The last-exit masses sum to one for every finite set containing the start. -/
theorem finiteLastExit_mass (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x : Γ) (hx : x ∈ A) :
    (∑ a : A, infiniteWalkLaw s μ hμ hmass (walkLastExitEver s (A : Set Γ) x a)) = 1 := by
  have hm (a : A) := measurableSet_walkLastExitEver s (A : Set Γ) A.measurableSet x a
  have hd : Pairwise (fun a b : A => Disjoint (walkLastExitEver s (A : Set Γ) x a)
      (walkLastExitEver s (A : Set Γ) x b)) := by
    intro a b hab
    exact walkLastExitEver_disjoint s (A : Set Γ) x (fun he => hab (Subtype.ext he))
  have hp := (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hm)).mp
    (walkLastExitEver_ae_cover s μ hμ hmass hgap A x hx)
  rw [measure_iUnion hd hm, tsum_fintype] at hp
  exact hp

/-- The actual finite last-exit distribution as a probability mass function. -/
def finiteLastExitLaw (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x : Γ) (hx : x ∈ A) : PMF A :=
  PMF.ofFintype (fun a => infiniteWalkLaw s μ hμ hmass (walkLastExitEver s (A : Set Γ) x a))
    (finiteLastExit_mass s μ hμ hmass hgap A x hx)

/-- The Green-times-escape formula for the actual probability mass function. -/
theorem finiteLastExitLaw_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x : Γ) (hx : x ∈ A) (a : A) :
    finiteLastExitLaw s μ hμ hmass hgap A x hx a = ENNReal.ofReal (walkGreen s μ x a) *
      infiniteWalkLaw s μ hμ hmass (walkNoReturnEvent s (A : Set Γ) a) :=
  walkLastExitEver_probability s μ hμ hmass hgap (A : Set Γ) A.measurableSet x a a.property

/-- Changing the starting state has exactly the finite Martin quotient as
its likelihood factor; zero no-return masses cause no difficulty. -/
theorem finiteLastExitLaw_martin_density (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Finset Γ) (o x : Γ) (ho : o ∈ A) (hx : x ∈ A) (a : A) :
    finiteLastExitLaw s μ (fun g hg => (hpos g hg).le) hmass hgap A x hx a =
      ENNReal.ofReal (martinQuotient s μ o x a) *
        finiteLastExitLaw s μ (fun g hg => (hpos g hg).le) hmass hgap A o ho a := by
  rw [finiteLastExitLaw_apply, finiteLastExitLaw_apply, ← mul_assoc,
    ← ENNReal.ofReal_mul (martinQuotient_pos s μ hpos hgen hgap o x a).le]
  rw [martinQuotient, div_mul_cancel₀ _ (walkGreen_ne_zero s μ hpos hgen hgap o a)]

end Singularity
