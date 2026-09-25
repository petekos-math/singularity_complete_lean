import Singularity.StationaryQuasiInvariant
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Measurable construction and uniqueness of the boundary law

Assuming almost every path has a limit in a metrizable Borel compactification,
we choose that limit, prove its almost-everywhere measurability, and select a
measurable version. Under an equivariant continuous action its distribution is
stationary and, for semigroup-generating positive support, quasi-invariant.
Convergence itself is not assumed silently: it remains an explicit hypothesis.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
variable {B : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    [PseudoMetrizableSpace B]

/-- The selected limit of the orbit path, with an arbitrary value on divergent samples. -/
def walkPathLimit (s : Finset Γ) (orbit : Γ → B) (ω : ℕ → s) : B :=
  letI : Nonempty B := ⟨orbit 1⟩
  Filter.limUnder atTop (fun n => orbit (walkPosition s 1 n ω))

omit [TopologicalSpace B] [BorelSpace B] [PseudoMetrizableSpace B] in
/-- Finite support makes orbit observations measurable even without any regularity of orbit. -/
theorem measurable_walkOrbitPosition (s : Finset Γ) (orbit : Γ → B) (n : ℕ) :
    Measurable (fun ω => orbit (walkPosition s 1 n ω)) :=
  (measurable_of_countable (fun w => orbit (walkEndpoint s n 1 w))).comp
    (measurable_walkPrefix s n)

omit [MeasurableSingletonClass Γ] [MeasurableSpace B] [BorelSpace B] [PseudoMetrizableSpace B] in
/-- Existence of almost-sure limits implies convergence to the selected limit. -/
theorem walkPathLimit_tendsto (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (orbit : Γ → B)
    (hconv : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      ∃ ξ : B, Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds ξ)) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds (walkPathLimit s orbit ω)) := by
  filter_upwards [hconv] with ω hω
  exact tendsto_nhds_limUnder hω

/-- The selected limit is almost everywhere measurable under actual path convergence. -/
theorem aemeasurable_walkPathLimit (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (orbit : Γ → B)
    (hconv : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      ∃ ξ : B, Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds ξ)) :
    AEMeasurable (walkPathLimit s orbit) (infiniteWalkLaw s μ hμ hmass) :=
  aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (measurable_walkOrbitPosition s orbit n).aemeasurable)
    (walkPathLimit_tendsto s μ hμ hmass orbit hconv)

/-- A measurable version of the path limit exists; convergence requires no separately chosen map. -/
theorem exists_measurable_walkLimit (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (orbit : Γ → B)
    (hconv : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      ∃ ξ : B, Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds ξ)) :
    ∃ b : (ℕ → s) → B, Measurable b ∧
      ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
        Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds (b ω)) := by
  have hm := aemeasurable_walkPathLimit s μ hμ hmass orbit hconv
  refine ⟨hm.mk (walkPathLimit s orbit), hm.measurable_mk, ?_⟩
  filter_upwards [walkPathLimit_tendsto s μ hμ hmass orbit hconv, hm.ae_eq_mk] with ω hω he
  rwa [he] at hω

variable [T2Space B]

omit [MeasurableSingletonClass Γ] [MeasurableSpace B] [BorelSpace B] [PseudoMetrizableSpace B] in
/-- Any two almost-sure path limits agree on a common full-measure set. -/
theorem walkBoundaryLimit_ae_unique (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (orbit : Γ → B)
    (b c : (ℕ → s) → B)
    (hb : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds (b ω)))
    (hc : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds (c ω))) :
    b =ᵐ[infiniteWalkLaw s μ hμ hmass] c := by
  filter_upwards [hb, hc] with ω hω kω
  exact tendsto_nhds_unique hω kω

omit [MeasurableSingletonClass Γ] [BorelSpace B] [PseudoMetrizableSpace B] in
/-- The distribution of a path limit is independent of all choices on null sets. -/
theorem walkBoundaryLaw_unique (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (orbit : Γ → B)
    (b c : (ℕ → s) → B)
    (hb : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds (b ω)))
    (hc : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds (c ω))) :
    walkBoundaryLaw s μ hμ hmass b = walkBoundaryLaw s μ hμ hmass c :=
  Measure.map_congr (walkBoundaryLimit_ae_unique s μ hμ hmass orbit b c hb hc)

variable [MulAction Γ B] [ContinuousConstSMul Γ B] [MeasurableSMul₂ Γ B]

/-- Path convergence constructs a stationary probability law whose translates are equivalent. -/
theorem exists_stationary_walkLimit (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (orbit : Γ → B) (horbit : ∀ g h, orbit (g * h) = g • orbit h)
    (hconv : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      ∃ ξ : B, Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds ξ)) :
    ∃ b : (ℕ → s) → B, Measurable b ∧
      (∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
        Tendsto (fun n => orbit (walkPosition s 1 n ω)) atTop (nhds (b ω))) ∧
      let ν := walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b
      IsProbabilityMeasure ν ∧
      ν = (∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun ξ : B => (g : Γ) • ξ) ν) ∧
      ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν ∧
        ν ≪ Measure.map (fun ξ : B => g • ξ) ν := by
  let hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨b, hb, hl⟩ := exists_measurable_walkLimit s μ hμ hmass orbit hconv
  have hs := walkBoundaryLaw_stationary_of_tendsto s μ hμ hmass orbit horbit b hb hl
  exact ⟨b, hb, hl, walkBoundaryLaw_probability s μ hμ hmass b hb, hs,
    stationary_translate_equivalent s μ hpos hgen _ hs⟩

end Singularity
