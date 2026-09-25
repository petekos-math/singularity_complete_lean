import Singularity.CayleyCompactification
import Singularity.BoundaryPairs

/-!
# Circle coordinates on the complete real-projective boundary

The Cayley transformation sends infinity to 1 and a real endpoint x to
(x-i)/(x+i). Its compact-sphere realization proves continuity and injectivity
without choosing a discontinuous real boundary chart. The squared chordal
distance gives the explicit denominator of the Liouville reference kernel.
-/

noncomputable section
open Set OnePoint
open scoped Classical Topology

namespace Singularity

/-- The Cayley circle coordinate, including the endpoint at infinity. -/
def boundaryCircle (p : OnePoint ℝ) : ℂ := p.elim 1 (fun x => ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I))

theorem boundaryCircle_infty : boundaryCircle ∞ = 1 := rfl

theorem boundaryCircle_coe (x : ℝ) :
    boundaryCircle (x : OnePoint ℝ) = ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I) := rfl

theorem boundaryCircle_denominator_ne_zero (x : ℝ) : (x : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

/-- The explicit circle coordinate is the restriction of the compact Cayley homeomorphism. -/
theorem boundaryCircle_compact (p : OnePoint ℝ) :
    (boundaryCircle p : OnePoint ℂ) = cayleyCompactHomeomorph (compactBoundaryEmbedding p) := by
  cases p with
  | infty =>
    change ((1 : ℂ) : OnePoint ℂ) = cayleyMatrix • (∞ : OnePoint ℂ)
    rw [OnePoint.smul_infty_eq_ite]
    change ((1 : ℂ) : OnePoint ℂ) = if (1 : ℂ) = 0 then ∞ else ((1 : ℂ) / 1 : ℂ)
    norm_num
  | coe x =>
    change (((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I) : OnePoint ℂ) =
      cayleyMatrix • ((x : ℂ) : OnePoint ℂ)
    rw [OnePoint.smul_some_eq_ite]
    change _ = if (1 : ℂ) * (x : ℂ) + Complex.I = 0 then ∞ else
      ((((1 : ℂ) * (x : ℂ) + -Complex.I) / ((1 : ℂ) * (x : ℂ) + Complex.I) : ℂ) : OnePoint ℂ)
    simp only [one_mul, boundaryCircle_denominator_ne_zero, ite_false, ← sub_eq_add_neg]

/-- Circle coordinates vary continuously across the finite-chart infinity point. -/
theorem continuous_boundaryCircle : Continuous boundaryCircle := by
  apply OnePoint.isOpenEmbedding_coe.isEmbedding.continuous_iff.mpr
  have h := cayleyCompactHomeomorph.continuous.comp continuous_compactBoundaryEmbedding
  simpa only [← boundaryCircle_compact, Function.comp_def] using h

/-- Distinct projective endpoints have distinct circle coordinates. -/
theorem boundaryCircle_injective : Function.Injective boundaryCircle := by
  intro p q hpq
  apply compactBoundaryEmbedding_injective
  apply cayleyCompactHomeomorph.injective
  rw [← boundaryCircle_compact, ← boundaryCircle_compact, hpq]

/-- The compact Cayley coordinate lies on the Euclidean unit circle. -/
theorem boundaryCircle_norm_one (p : OnePoint ℝ) : ‖boundaryCircle p‖ = 1 := by
  cases p with
  | infty => simp only [boundaryCircle_infty, norm_one]
  | coe x =>
    rw [boundaryCircle_coe, norm_div]
    have hn : ‖(x : ℂ) - Complex.I‖ = ‖(x : ℂ) + Complex.I‖ := by
      simpa only [map_add, Complex.conj_ofReal, Complex.conj_I, ← sub_eq_add_neg] using
        Complex.norm_conj ((x : ℂ) + Complex.I)
    rw [hn, div_self (norm_ne_zero_iff.mpr (boundaryCircle_denominator_ne_zero x))]

/-- Exact complex difference formula for finite endpoints. -/
theorem boundaryCircle_sub (x y : ℝ) :
    boundaryCircle (x : OnePoint ℝ) - boundaryCircle (y : OnePoint ℝ) =
      (2 * Complex.I) * ((x : ℂ) - (y : ℂ)) / (((x : ℂ) + Complex.I) * ((y : ℂ) + Complex.I)) := by
  simp only [boundaryCircle_coe]
  field_simp [boundaryCircle_denominator_ne_zero x, boundaryCircle_denominator_ne_zero y]
  ring

/-- Squared chordal distance in the finite real chart. -/
theorem boundaryCircle_dist_sq (x y : ℝ) :
    dist (boundaryCircle (x : OnePoint ℝ)) (boundaryCircle (y : OnePoint ℝ)) ^ 2 =
      4 * (x - y) ^ 2 / ((x ^ 2 + 1) * (y ^ 2 + 1)) := by
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, boundaryCircle_sub]
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul]
  simp [Complex.normSq_apply, pow_two]
  ring

end Singularity
