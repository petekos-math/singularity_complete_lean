import Singularity.CocycleDeficitShadows
import Singularity.FuchsianLogCocycle

/-!
# Concrete Green-deficit shadows for the actual hitting measure

The deficit uses the original Green distance and actual Radon–Nikodym
cocycle. The local cocycle bound and shadow estimates are proved, not inputs.
Uniform mass of inverse shadows and exceptional-set geometry remain open.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical MatrixGroups UpperHalfPlane ENNReal Topology
namespace Singularity

variable (Γ : Subgroup PSL(2, ℝ)) [MeasurableSpace Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (z : ℍ)

/-- The actual Green-deficit shadow, in target boundary coordinates. -/
def fuchsianGreenDeficitShadow (R : ℝ) (g : Γ) : Set (OnePoint ℝ) :=
  cocycleDeficitShadow (projectiveHittingMeasure Γ s z μ hpos hmass)
    (fun a => greenDistance s μ 1 a) R g

/-- Every Green-deficit shadow is a measurable boundary set. -/
theorem measurableSet_fuchsianGreenDeficitShadow (R : ℝ) (g : Γ) :
    MeasurableSet (fuchsianGreenDeficitShadow Γ s μ hpos hmass z R g) :=
  measurableSet_cocycleDeficitShadow _ _ _ _

/-- Increasing the deficit parameter enlarges each actual harmonic candidate. -/
theorem fuchsianGreenDeficitShadow_mono (g : Γ) :
    Monotone (fun R => fuchsianGreenDeficitShadow Γ s μ hpos hmass z R g) :=
  cocycleDeficitShadow_mono _ _ _

variable [DiscreteTopology Γ] [MeasurableSingletonClass Γ]
variable (hne : ProjectiveNonelementary Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
include hne hgen

/-- The defining Green approximation holds simultaneously for every group
element and every nonnegative parameter on a common conull set. -/
theorem fuchsianGreenDeficitShadow_logCocycle_bound :
    ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass, ∀ g : Γ, ∀ R : ℝ, 0 ≤ R →
      g • ξ ∈ fuchsianGreenDeficitShadow Γ s μ hpos hmass z R g →
      |stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) g ξ -
        greenDistance s μ 1 g| ≤ R := by
  filter_upwards [fuchsian_logCocycle_green_bounds Γ hne s μ hpos hmass hgen z] with ξ hξ
  intro g R hR hmem
  change greenDistance s μ 1 g -
    stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) g (g⁻¹ • (g • ξ)) ≤ R at hmem
  rw [inv_smul_smul] at hmem
  exact abs_le.mpr ⟨by linarith, by linarith [(hξ g).2]⟩

/-- Actual shadow masses satisfy the exponential Green estimates multiplied
by inverse-shadow mass; a uniform positive lower bound is not inferred. -/
theorem fuchsianGreenDeficitShadow_mass_bounds (g : Γ) {R : ℝ} (hR : 0 ≤ R) :
    let ν := projectiveHittingMeasure Γ s z μ hpos hmass
    let A := {ξ | greenDistance s μ 1 g - stationaryLogCocycle ν g ξ ≤ R}
    ENNReal.ofReal (Real.exp (-greenDistance s μ 1 g - R)) * ν A ≤
        ν (fuchsianGreenDeficitShadow Γ s μ hpos hmass z R g) ∧
      ν (fuchsianGreenDeficitShadow Γ s μ hpos hmass z R g) ≤
        ENNReal.ofReal (Real.exp (-greenDistance s μ 1 g + R)) * ν A := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  apply cocycleDeficitShadow_mass_bounds _
    (fun a => (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z a).1)
    (fun a => greenDistance s μ 1 a) g hR
  filter_upwards [fuchsian_logCocycle_green_bounds Γ hne s μ hpos hmass hgen z] with ξ hξ
  exact (hξ g).2

/-- The two directed Green bounds give an explicit conull threshold for each
fixed group element. This threshold may grow with the group element. -/
theorem fuchsianGreenDeficitShadow_conull_of_directed_bound
    (g : Γ) {R : ℝ} (hR : greenDistance s μ 1 g + greenDistance s μ g 1 ≤ R) :
    ∀ᵐ ξ ∂projectiveHittingMeasure Γ s z μ hpos hmass,
      g • ξ ∈ fuchsianGreenDeficitShadow Γ s μ hpos hmass z R g := by
  filter_upwards [fuchsian_logCocycle_green_bounds Γ hne s μ hpos hmass hgen z] with ξ hξ
  change greenDistance s μ 1 g -
    stationaryLogCocycle (projectiveHittingMeasure Γ s z μ hpos hmass) g (g⁻¹ • (g • ξ)) ≤ R
  rw [inv_smul_smul]
  linarith [(hξ g).1]

end Singularity
