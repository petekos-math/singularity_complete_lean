import Singularity.CayleyMetric

/-!
# Disk limits at finite real boundary points

The Cayley formula extends continuously to every real boundary coordinate, and
its boundary restriction is injective. No geometric Martin identification is
used in these elementary boundary-coordinate statements.
-/

noncomputable section
open Filter
open scoped Topology UpperHalfPlane
namespace Singularity

def realBoundaryCayley (ξ : ℝ) : ℂ := ((ξ : ℂ) - Complex.I) / ((ξ : ℂ) + Complex.I)

theorem realBoundaryCayley_denominator_ne_zero (ξ : ℝ) : (ξ : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi

theorem realBoundaryCayley_injective : Function.Injective realBoundaryCayley := by
  intro ξ η h
  unfold realBoundaryCayley at h
  have he := (div_eq_div_iff (realBoundaryCayley_denominator_ne_zero ξ)
    (realBoundaryCayley_denominator_ne_zero η)).mp h
  have hp : ((ξ : ℂ) - (η : ℂ)) * Complex.I = 0 := by linear_combination he / 2
  exact Complex.ofReal_injective (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right Complex.I_ne_zero))

/-- Convergence to a finite real point implies convergence to its disk boundary coordinate. -/
theorem halfPlaneCayley_tendsto_real {α : Type*} {l : Filter α} (z : α → ℍ) (ξ : ℝ)
    (hz : Tendsto (fun n => (z n : ℂ)) l (𝓝 (ξ : ℂ))) :
    Tendsto (fun n => halfPlaneCayley (z n)) l (𝓝 (realBoundaryCayley ξ)) :=
  (hz.sub tendsto_const_nhds).div (hz.add tendsto_const_nhds)
    (realBoundaryCayley_denominator_ne_zero ξ)

end Singularity
