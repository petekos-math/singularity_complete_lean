import Singularity.FuchsianMixedDeficitUniformMass
import Singularity.FuchsianMixedDeficitEstimates
import Singularity.FuchsianShadowGeometryRigidity
import Singularity.FuchsianVisualCarrier
import Singularity.FuchsianShadowCorrections
import Singularity.FuchsianGreenRigidityReduction

/-!
# Singularity conditional on deficit compactness

The common shadows, mass estimates, cocycle estimates, finite corrections,
and path coverage are assembled internally. The sole additional geometric
premise is `FuchsianDeficitCompactness`. Its geometric construction for the
remaining noncompact case is provided in `FuchsianDirichletDeficit`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal Topology
namespace Singularity

/-- Deficit compactness implies singularity for the actual Fuchsian hitting
law. This intermediate theorem takes deficit compactness as an input; the
final theorem supplies it from geometric hypotheses. -/
theorem fuchsian_hittingMeasure_singular_of_deficit_compactness
    (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (hne : ProjectiveNonelementary Γ)
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)
    (hcompact : FuchsianDeficitCompactness Γ s μ hpos hmass z) :
    projectiveHittingMeasure Γ s z μ hpos hmass ⟂ₘ compactPoissonMeasure z := by
  by_contra hns
  let ν := projectiveHittingMeasure Γ s z μ hpos hmass
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  let := compactPoissonMeasure_probability z
  have hac := fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular
    Γ hne s μ hpos hmass hgen z hns
  obtain ⟨E, r, C, hE, _, hEpos, hinv, hνm, hmν, _, _, hmq, _, heq⟩ :=
    fuchsian_hittingMeasure_visualCarrier_shadow_data Γ hne s μ hpos hmass hgen z hns
  let m := (compactPoissonMeasure z).restrict E
  obtain ⟨Nν, cν, hcν, hcν1, hνmass⟩ :=
    fuchsianMixedDeficitShadow_positive_inverse_mass_of_compactness
      Γ hne s μ hpos hmass hgen z hcompact ν (Measure.AbsolutelyContinuous.rfl) hac
      (by simp [ν]) (by simp [ν])
  obtain ⟨Nm, cm, hcm, hcm1, hmmass⟩ :=
    fuchsianMixedDeficitShadow_positive_inverse_mass_of_compactness
      Γ hne s μ hpos hmass hgen z hcompact m hmν Measure.absolutelyContinuous_restrict
      (by simpa [m] using hEpos)
      ((Measure.restrict_le_self _).trans (by simp))
  let N₀ := max Nν Nm
  let S : ℕ → Γ → Set (OnePoint ℝ) :=
    fun k => fuchsianMixedDeficitShadow Γ s μ hpos hmass z (N₀ + k)
  have hνestimate (k : ℕ) := fuchsianMixedDeficitShadow_hitting_estimates
    Γ s μ hpos hmass z hne hgen (N₀ + k) hcν hcν1
    (hνmass _ (by dsimp [N₀]; omega))
  have hmestimate (k : ℕ) := fuchsianMixedDeficitShadow_carrier_estimates
    Γ s μ hpos hmass z hE hinv (N₀ + k) hcm hcm1
    (hmmass _ (by dsimp [N₀]; omega))
  have hcorrection (F : Finset Γ) : ∃ J : ℝ, ∀ᵐ ξ ∂ν, ∀ a ∈ F,
      |stationaryLogCocycle ν a ξ - stationaryLogCocycle m a ξ| ≤ J := by
    obtain ⟨J, _, hJ⟩ := fuchsian_finite_cocycle_difference_bound Γ hne s μ hpos hmass hgen z hns F
    refine ⟨J, ?_⟩
    filter_upwards [hJ, heq] with ξ hξ he
    intro a ha
    rw [(he a).1]
    exact hξ a ha
  have hcoverage : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      ∃ k : ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : Finset Γ,
        ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∀ᶠ n in atTop,
          walkPosition s 1 (φ n) ω • (a⁻¹ • ξ) ∈ S k (walkPosition s 1 (φ n) ω) := by
    apply Eventually.of_forall
    intro ω
    obtain ⟨N, φ, hφ, F, hF⟩ := fuchsianMixedDeficitShadow_ae_cover_of_compactness
      Γ hne s μ hpos hmass hgen z hcompact (fun n => walkPosition s 1 n ω)
    refine ⟨N, φ, hφ, F, ?_⟩
    filter_upwards [hF] with ξ hξ
    obtain ⟨a, ha, h⟩ := hξ
    refine ⟨a, ha, ?_⟩
    filter_upwards [h] with n hn
    exact fuchsianMixedDeficitShadow_mono Γ s μ hpos hmass z _ (Nat.le_add_left N N₀) hn
  obtain ⟨L, hL⟩ := fuchsian_magnitude_rigidity_from_shadow_geometry Γ hne s μ hpos hmass hgen z
    m hνm hmν hmq S (fun k g => measurableSet_fuchsianMixedDeficitShadow Γ s μ hpos hmass z _ g)
    (fun g => greenDistance s μ 1 g) (fun g => dist z (g • z))
    (fun k => ((N₀ + k : ℕ) : ℝ) - Real.log cν)
    (fun k => Real.log (verticalShadowFactor (1 / (((N₀ + k : ℕ) : ℝ) + 1))) - Real.log cm)
    (fun k g => (hνestimate k g).1.1) (fun k g => (hνestimate k g).1.2)
    (fun k g => (hmestimate k g).1.1) (fun k g => (hmestimate k g).1.2)
    (fun k g => (hνestimate k g).2) (fun k g => (hmestimate k g).2)
    hcorrection hcoverage
  apply hns
  apply fuchsian_hittingMeasure_singular_of_green_upper Γ hne s μ hpos hmass hgen z 1 L zero_lt_one
  intro g
  have h := (abs_le.mp (hL g)).2
  linarith

end Singularity
