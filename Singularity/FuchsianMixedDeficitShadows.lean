import Singularity.FuchsianGreenDeficitShadows
import Singularity.MixedVisualExceptionalLimit
import Singularity.VisualShadowSize

/-!
# A countable common Green/visual shadow family

The nth shadow uses Green-deficit allowance n and visual cap 1/(n+1).
This diagonal family is cofinal in both parameters. Consequently the proved
visual exceptional convergence combines with a harmonic exceptional-set
hypothesis to give exactly the countable coverage used by rigidity.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal Topology
namespace Singularity

/-- A single natural index can enlarge both a deficit allowance and a visual
shadow. This is the cofinality needed for simultaneous pathwise estimates. -/
theorem exists_nat_shadow_parameters (R : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, R ≤ (N : ℝ) ∧ 1 / ((N : ℝ) + 1) ≤ r := by
  obtain ⟨n, hn⟩ := exists_nat_ge R
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
  refine ⟨max n m, hn.trans (by exact_mod_cast le_max_left n m), ?_⟩
  apply le_trans ?_ hm.le
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1)
  have hreal : (m : ℝ) ≤ (max n m : ℕ) := by exact_mod_cast le_max_right n m
  linarith

variable (Γ : Subgroup PSL(2, ℝ)) [MeasurableSpace Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (z : ℍ)

/-- The canonical countable mixed shadow built from the actual hitting law. -/
def fuchsianMixedDeficitShadow (N : ℕ) (g : Γ) : Set (OnePoint ℝ) :=
  fuchsianGreenDeficitShadow Γ s μ hpos hmass z N g ∩
    visualShadow z (g • z) (1 / ((N : ℝ) + 1))

/-- The canonical common shadow is measurable. -/
theorem measurableSet_fuchsianMixedDeficitShadow (N : ℕ) (g : Γ) :
    MeasurableSet (fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g) :=
  (measurableSet_fuchsianGreenDeficitShadow Γ s μ hpos hmass z N g).inter
    (isOpen_visualShadow _ _ _).measurableSet

/-- The integer-indexed common shadows increase with the parameter. -/
theorem fuchsianMixedDeficitShadow_mono (g : Γ) :
    Monotone (fun N => fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g) := by
  intro n m hnm
  apply inter_subset_inter
  · exact fuchsianGreenDeficitShadow_mono Γ s μ hpos hmass z g (by exact_mod_cast hnm)
  · apply visualShadow_antitone z (g • z)
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    have hreal : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith

/-- Any prescribed pair of harmonic and positive visual parameters is
contained in one member of the canonical countable family, uniformly in g. -/
theorem fuchsianMixedDeficitShadow_cofinal (R : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ g : Γ,
      fuchsianGreenDeficitShadow Γ s μ hpos hmass z R g ∩ visualShadow z (g • z) r ⊆
        fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g := by
  obtain ⟨N, hR, hrN⟩ := exists_nat_shadow_parameters R hr
  exact ⟨N, fun g => inter_subset_inter
    (fuchsianGreenDeficitShadow_mono Γ s μ hpos hmass z g hR)
    (visualShadow_antitone z (g • z) hrN)⟩

variable [DiscreteTopology Γ] [MeasurableSingletonClass Γ]

/-- The harmonic cocycle approximation is proved for the concrete mixed
family, simultaneously over every group element and every integer index. -/
theorem fuchsianMixedDeficitShadow_logCocycle_bound
    (hne : ProjectiveNonelementary Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass, ∀ N : ℕ, ∀ g : Γ,
      g • ξ ∈ fuchsianMixedDeficitShadow Γ s μ hpos hmass z N g →
      |stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) g ξ -
        greenDistance s μ 1 g| ≤ (N : ℝ) := by
  filter_upwards [fuchsianGreenDeficitShadow_logCocycle_bound Γ s μ hpos hmass z hne hgen]
    with ξ hξ
  exact fun N g hmem => hξ g N (Nat.cast_nonneg N) hmem.1

omit [DiscreteTopology Γ] [MeasurableSingletonClass Γ] in
/-- The remaining harmonic exceptional-set property supplies finite eventual
coverage for the explicit countable mixed family. The visual geometry and
parameter cofinality are proved internally. -/
theorem fuchsianMixedDeficitShadow_finite_eventual_cover
    (hne : ProjectiveNonelementary Γ) (g : ℕ → Γ) {Z : Set (OnePoint ℝ)} (hZ : Z.Finite)
    (hshrink : ∀ U : Set (OnePoint ℝ), IsOpen U → Z ⊆ U → ∃ R : ℝ,
      ∀ᶠ n in atTop, ((fun ξ : OnePoint ℝ => g n • ξ) ⁻¹'
        fuchsianGreenDeficitShadow Γ s μ hpos hmass z R (g n))ᶜ ⊆ U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ N : ℕ, ∃ F : Finset Γ,
      ∀ ξ : OnePoint ℝ, ∃ a ∈ F, ∀ᶠ n in atTop,
        g (φ n) • (a⁻¹ • ξ) ∈ fuchsianMixedDeficitShadow Γ s μ hpos hmass z N (g (φ n)) := by
  obtain ⟨φ, hφ, R, r, hr, F, hF⟩ := fuchsian_mixed_visualShadow_finite_eventual_cover
    Γ hne g z (fun R n => fuchsianGreenDeficitShadow Γ s μ hpos hmass z R (g n)) hZ hshrink
  obtain ⟨N, hN⟩ := fuchsianMixedDeficitShadow_cofinal Γ s μ hpos hmass z R hr
  refine ⟨φ, hφ, N, F, fun ξ => ?_⟩
  obtain ⟨a, ha, hξ⟩ := hF ξ
  refine ⟨a, ha, ?_⟩
  filter_upwards [hξ] with n hn
  exact hN (g (φ n)) hn

end Singularity
