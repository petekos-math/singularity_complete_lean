import Singularity.FuchsianShadowPathComparison
import Singularity.BoundedSequenceShadowRigidity
import Singularity.TranslatedConcentrationReturnCover

/-!
# Rigidity from common shadow geometry for the actual Fuchsian walk

The proof constructs a positive bounded-density event and chooses an actual
walk path. Pathwise concentration yields bounded magnitude discrepancy and
all return errors. Only common exponential/cocycle shadow estimates, eventual
geometric coverage, and finite correction bounds remain inputs.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal Topology
namespace Singularity

/-- Global magnitude rigidity for the actual walk, with no differentiation,
mass-ratio, preselected path, density-window, or return-error hypothesis.
The common shadow geometry and finite correction bounds remain explicit.
A countable family allows the shadow parameter to be chosen after the path. -/
theorem fuchsian_magnitude_rigidity_from_shadow_geometry {I : Type*} [Countable I]
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (m : Measure (OnePoint ℝ)) [IsFiniteMeasure m]
    (hνm : projectiveHittingMeasure Γ s z μ hpos hmass ≪ m)
    (hmν : m ≪ projectiveHittingMeasure Γ s z μ hpos hmass)
    (hmq : ∀ a : Γ, Measure.map (fun ξ : OnePoint ℝ => a • ξ) m ≪ m)
    (S : I → Γ → Set (OnePoint ℝ)) (hS : ∀ i a, MeasurableSet (S i a))
    (Dν Dm : Γ → ℝ) (Cν Cm : I → ℝ)
    (hνl : ∀ i a, ENNReal.ofReal (Real.exp (-Dν a - Cν i)) ≤
      projectiveHittingMeasure Γ s z μ hpos hmass (S i a))
    (hνu : ∀ i a, projectiveHittingMeasure Γ s z μ hpos hmass (S i a) ≤
      ENNReal.ofReal (Real.exp (-Dν a + Cν i)))
    (hml : ∀ i a, ENNReal.ofReal (Real.exp (-Dm a - Cm i)) ≤ m (S i a))
    (hmu : ∀ i a, m (S i a) ≤ ENNReal.ofReal (Real.exp (-Dm a + Cm i)))
    (hνshadow : ∀ i a, ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
      a • ξ ∈ S i a →
        |stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) a ξ - Dν a| ≤ Cν i)
    (hmshadow : ∀ i a, ∀ᵐ ξ ∂m, a • ξ ∈ S i a → |stationaryLogCocycle m a ξ - Dm a| ≤ Cm i)
    (hcorrection : ∀ F : Finset Γ, ∃ J : ℝ,
      ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass, ∀ a ∈ F,
        |stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) a ξ -
          stationaryLogCocycle m a ξ| ≤ J)
    (hcoverage : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      ∃ i : I, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : Finset Γ,
        ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass, ∃ a ∈ F, ∀ᶠ n in atTop,
          walkPosition s 1 (φ n) ω • (a⁻¹ • ξ) ∈ S i (walkPosition s 1 (φ n) ω)) :
    ∃ C : ℝ, ∀ a : Γ, |Dν a - Dm a| ≤ C := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let ν := projectiveHittingMeasure Γ s z μ hpos hmass
  let P := infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass
  let b := projectiveBoundaryMap Γ s z
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  have hνq (a : Γ) : Measure.map (fun ξ : OnePoint ℝ => a • ξ) ν ≪ ν :=
    (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z a).1
  obtain ⟨M, _, hpositive⟩ := exists_positive_logDensity_window ν m
    (by rw [measure_univ]; exact zero_lt_one)
  let E : Set (OnePoint ℝ) := {ξ | |Real.log ((ν.rnDeriv m ξ).toReal)| ≤ M}
  have hE : MeasurableSet E := measurableSet_logDensity_window ν m M
  have hwindow : ∀ ξ ∈ E, |Real.log ((ν.rnDeriv m ξ).toReal)| ≤ M := fun _ h => h
  have hcompare := ae_all_iff.mpr (fun i : I =>
    fuchsian_shadow_path_magnitude_comparison Γ hne s μ hpos hmass hgen z
      m hνm hmν hmq (S i) (hS i) Dν Dm (Cν i) (Cm i)
      (hνl i) (hνu i) (hml i) (hmu i) (hνshadow i) (hmshadow i) hE M hwindow)
  have hcon := fuchsian_hittingMeasure_complement_concentration Γ hne s μ hpos hmass hgen z hE
  have hp : P (b ⁻¹' E) ≠ 0 := by
    have he : ν E = P (b ⁻¹' E) := Measure.map_apply (measurable_projectiveBoundaryMap Γ s z) hE
    exact (he ▸ hpositive).ne'
  obtain ⟨ω, hωE, hω⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp
    (ae_restrict_of_ae ((hcompare.and hcon).and hcoverage))
  obtain ⟨i, φ, hφ, F, hF⟩ := hω.2
  obtain ⟨L, hL⟩ := hω.1.1 i hωE
  obtain ⟨J, hJ⟩ := hcorrection F
  have hreturn := shadow_return_cover_of_translated_concentration ν hνq
    (fun n => walkPosition s 1 (φ n) ω) (fun n => S i (walkPosition s 1 (φ n) ω)) E F
    ((hω.1.2 hωE).comp hφ.tendsto_atTop) hF
  apply magnitude_rigidity_of_bounded_sequence_return_cover ν m hνm hmν hνq hmq
    (S i) Dν Dm (Cν i) (Cm i) (hνl i) (hνu i) (hml i) (hmu i)
    (ae_all_iff.mpr (hνshadow i)) (hνm.ae_le (ae_all_iff.mpr (hmshadow i)))
    (fun n => walkPosition s 1 (φ n) ω) L (fun n => hL (φ n)) F M J hJ
  filter_upwards [hreturn] with ξ hξ
  obtain ⟨a, ha, n, hn⟩ := hξ
  exact ⟨a, ha, n, hn.1, hwindow _ hn.2⟩

end Singularity
