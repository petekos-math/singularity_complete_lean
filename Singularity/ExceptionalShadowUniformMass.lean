import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Uniform inverse mass from exceptional-set subsequence compactness

For an increasing shadow family, a sequence contradicting uniform exhaustion
would have a subsequence whose complements eventually lie almost everywhere
in any neighborhood of a finite exceptional set. For an atomless outer
regular measure such a neighborhood has arbitrarily small mass, a contradiction.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal Topology
namespace Singularity

/-- Exceptional-set compactness for every sequence implies uniform exhaustion
in measure. The pointwise-to-uniform inference uses the full subsequence
hypothesis and atomlessness; pointwise exhaustion alone is insufficient. -/
theorem uniform_shadow_mass_of_exceptional_subsequences
    {A B : Type*} [MeasurableSpace B] [TopologicalSpace B]
    (ν : Measure B) [Measure.OuterRegular ν] [NullSingletonClass ν]
    (T : ℕ → A → Set B) (hmono : ∀ a, Monotone (fun N => T N a))
    (hcompact : ∀ g : ℕ → A, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Z : Set B, Z.Finite ∧ ∀ U : Set B, IsOpen U → Z ⊆ U →
        ∃ R : ℕ, ∀ᶠ n in atTop, ∀ᵐ ξ ∂ν, ξ ∉ T R (g (φ n)) → ξ ∈ U)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a : A, ν ((T N a)ᶜ) < ε := by
  by_contra hnone
  push Not at hnone
  choose g hg using hnone
  obtain ⟨φ, hφ, Z, hZ, hconv⟩ := hcompact g
  obtain ⟨U, hZU, hU, hsmall⟩ := Z.exists_isOpen_lt_of_lt (μ := ν) ε (by simpa [hZ.measure_zero ν] using hε)
  obtain ⟨R, hR⟩ := hconv U hU hZU
  obtain ⟨n, hn, hlarge⟩ := (hR.and (hφ.tendsto_atTop.eventually (eventually_ge_atTop R))).exists
  have hmass : ν ((T R (g (φ n)))ᶜ) ≤ ν U := measure_mono_ae hn
  have hsub : (T (φ n) (g (φ n)))ᶜ ⊆ (T R (g (φ n)))ᶜ :=
    compl_subset_compl.mpr (hmono _ hlarge)
  exact (not_lt_of_ge (hg (φ n))) ((measure_mono hsub).trans hmass |>.trans_lt hsmall)

end Singularity
