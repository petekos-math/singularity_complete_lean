import Singularity.CayleyMetric

/-!
# The Cayley coordinate as a homeomorphism of the compact sphere

Euclidean convergence of disk coordinates yields convergence in the actual
compact sphere by applying the inverse projective Cayley transformation.
-/

noncomputable section
open Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- The invertible complex matrix defining the Cayley transformation. -/
def cayleyMatrix : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, -Complex.I; 1, Complex.I] (by
    norm_num [Matrix.det_fin_two, mul_two])

/-- Its projective transformation agrees with the disk coordinate on interior points. -/
theorem cayleyMatrix_smul_embedding (z : ℍ) :
    cayleyMatrix • hyperbolicCompactEmbedding z = (halfPlaneCayley z : OnePoint ℂ) := by
  rw [hyperbolicCompactEmbedding, OnePoint.smul_some_eq_ite]
  change (if (1 : ℂ) * (z : ℂ) + Complex.I = 0 then (∞ : OnePoint ℂ) else
    (((1 : ℂ) * (z : ℂ) + -Complex.I) / ((1 : ℂ) * (z : ℂ) + Complex.I) : ℂ)) = _
  simp only [one_mul, halfPlaneCayley_denominator_ne_zero, ite_false, ← sub_eq_add_neg,
    halfPlaneCayley]

/-- The Cayley transformation is a homeomorphism of the full compact sphere. -/
def cayleyCompactHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ := projectiveMobiusHomeomorph cayleyMatrix

/-- The inverse compact Cayley transformation recovers each interior point. -/
theorem cayleyCompactHomeomorph_symm (z : ℍ) :
    cayleyCompactHomeomorph.symm (halfPlaneCayley z : OnePoint ℂ) = hyperbolicCompactEmbedding z := by
  apply cayleyCompactHomeomorph.symm_apply_eq.mpr
  exact (cayleyMatrix_smul_embedding z).symm

/-- Convergence in the disk coordinate gives convergence in the compact sphere,
including the possibility that the limit is infinity. -/
theorem cayley_tendsto_compact {z : ℕ → ℍ} {q : ℂ}
    (hq : Tendsto (fun n => halfPlaneCayley (z n)) atTop (nhds q)) :
    Tendsto (fun n => hyperbolicCompactEmbedding (z n)) atTop
      (nhds (cayleyCompactHomeomorph.symm (q : OnePoint ℂ))) := by
  have h := (cayleyCompactHomeomorph.symm.continuous.tendsto (q : OnePoint ℂ)).comp
    (OnePoint.continuous_coe.tendsto q |>.comp hq)
  simpa only [Function.comp_def, cayleyCompactHomeomorph_symm] using h

end Singularity
