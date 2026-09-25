import Singularity.MartinAction
import Singularity.WeightedCurrent

/-!
# Conditional invariant currents on the actual Martin boundaries

Finite generation makes the boundary action Borel measurable. If measures on the
forward and reflected boundaries have the stated pushforward densities, and a
measurable real kernel has the Naïm covariance law, its nonnegative part weights
an invariant product measure. The derivative and full-kernel hypotheses are
explicit: this file does not construct hitting measures or prove those hypotheses.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ a ∈ s, 0 < μ a)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

/-- The constructed Martin-boundary homeomorphism is a Borel equivalence. -/
def martinBoundaryMeasurableEquiv (o g : Γ) :
    martinBoundary s μ o ≃ᵐ martinBoundary s μ o := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  exact (martinBoundaryHomeomorph s μ hpos hgen hgap o g).toMeasurableEquiv

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] in
include hgen in
/-- The actual normalization cocycle is measurable on the boundary. -/
theorem measurable_martinBoundaryCocycle (o g : Γ) :
    Measurable (martinBoundaryCocycle s μ o g) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  exact (continuous_martinBoundaryCocycle s μ o g).measurable

include hpos hgen hgap in
theorem martinBoundaryCocycle_one (o : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryCocycle s μ o 1 ξ = 1 := by
  simpa only [martinBoundaryCocycle, inv_one, one_mul] using
    martinBoundaryKernel_base s μ hpos hgen hgap o ξ

/-- Source and target normalization factors are reciprocal, with the action in
its precise position. -/
theorem martinBoundaryCocycle_inv_mul (o g : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryCocycle s μ o g⁻¹ (martinBoundaryMap s μ hpos hgen hgap o g ξ) *
      martinBoundaryCocycle s μ o g ξ = 1 := by
  rw [← martinBoundaryCocycle_mul, inv_mul_cancel, martinBoundaryCocycle_one s μ hpos hgen hgap]

/-- The weighted product on the reflected and forward Martin boundaries is
invariant, conditional on the derivative formulas and full kernel covariance.
The pushforward by `g` uses the cocycle at `g⁻¹`, evaluated at the target point. -/
theorem martin_weightedProduct_invariant (o : Γ)
    (νm : Measure (martinBoundary (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹) o))
    (νp : Measure (martinBoundary s μ o)) [SFinite νm] [SFinite νp]
    (K : martinBoundary (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹) o ×
      martinBoundary s μ o → ℝ) (hK : Measurable K)
    (hm : ∀ g : Γ, Measure.map (martinBoundaryMap
      (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹)
      (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
      (reflectedMarkov_spectral_gap s μ hgap) o g) νm =
      νm.withDensity (fun ξ => ENNReal.ofReal (martinBoundaryCocycle
        (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹) o g⁻¹ ξ)))
    (hp : ∀ g : Γ, Measure.map (martinBoundaryMap s μ hpos hgen hgap o g) νp =
      νp.withDensity (fun η => ENNReal.ofReal (martinBoundaryCocycle s μ o g⁻¹ η)))
    (hc : ∀ (g : Γ) z, K (martinBoundaryMap
      (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹)
      (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
      (reflectedMarkov_spectral_gap s μ hgap) o g z.1,
      martinBoundaryMap s μ hpos hgen hgap o g z.2) = K z /
      (martinBoundaryCocycle (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹) o g z.1 *
        martinBoundaryCocycle s μ o g z.2)) (g : Γ) :
    Measure.map (fun z => (martinBoundaryMap
      (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹)
      (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
      (reflectedMarkov_spectral_gap s μ hgap) o g z.1,
      martinBoundaryMap s μ hpos hgen hgap o g z.2))
      ((νm.prod νp).withDensity (fun z => ENNReal.ofReal (K z))) =
      (νm.prod νp).withDensity (fun z => ENNReal.ofReal (K z)) := by
  exact weightedProduct_invariant_of_div
    (martinBoundaryMeasurableEquiv (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹)
      (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
      (reflectedMarkov_spectral_gap s μ hgap) o g)
    (martinBoundaryMeasurableEquiv s μ hpos hgen hgap o g) νm νp
    (martinBoundaryCocycle (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹) o g⁻¹)
    (martinBoundaryCocycle s μ o g⁻¹) K
    (measurable_martinBoundaryCocycle _ _ (reflected_support_generates s hgen) o g⁻¹)
    (measurable_martinBoundaryCocycle s μ hgen o g⁻¹) hK
    (martinBoundaryCocycle_pos _ _ (reflected_jump_pos s μ hpos)
      (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap) o g⁻¹)
    (martinBoundaryCocycle_pos s μ hpos hgen hgap o g⁻¹)
    (hm g) (hp g) (Filter.Eventually.of_forall (hc g⁻¹))

end Singularity
