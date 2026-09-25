import Singularity.Markov
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Point masses and evaluation on counting-measure L²

For counting measure, a.e. equality is pointwise equality. The characteristic
function of a singleton represents the usual unit point mass in L².
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace Singularity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The unit point mass as an actual counting-measure L² vector. -/
def countingDelta (x : X) : GroupL2 X :=
  indicatorConstLp 2 (measurableSet_singleton x)
    (by rw [Measure.count_singleton]; exact ENNReal.one_ne_top) (1 : ℂ)

/-- Its representative is the characteristic function of the singleton. -/
theorem countingDelta_apply (x y : X) : countingDelta x y = if y = x then 1 else 0 := by
  classical
  have h := Measure.ae_count_iff.mp (indicatorConstLp_coeFn
    (p := 2) (hs := measurableSet_singleton x)
    (hμs := by rw [Measure.count_singleton]; exact ENNReal.one_ne_top) (c := (1 : ℂ))) y
  simpa only [countingDelta, Set.indicator_apply, Set.mem_singleton_iff] using h

/-- Unit point masses have norm one. -/
theorem countingDelta_norm (x : X) : ‖countingDelta x‖ = 1 := by
  rw [countingDelta, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [measureReal_def]

/-- Pairing with the unit point mass is point evaluation. -/
theorem countingDelta_inner (x : X) (f : GroupL2 X) : inner ℂ (countingDelta x) f = f x := by
  rw [countingDelta, L2.inner_indicatorConstLp_one, integral_singleton]
  simp [measureReal_def]

/-- Evaluation is bounded, as required to pass from operator to kernel convergence. -/
def countingEvaluation (x : X) : GroupL2 X →L[ℂ] ℂ := innerSL ℂ (countingDelta x)

theorem countingEvaluation_apply (x : X) (f : GroupL2 X) : countingEvaluation x f = f x :=
  countingDelta_inner x f

/-- The usual ℓ² point-evaluation estimate. -/
theorem countingEvaluation_le (x : X) (f : GroupL2 X) : ‖f x‖ ≤ ‖f‖ := by
  rw [← countingDelta_inner x f]
  simpa only [countingDelta_norm, one_mul] using norm_inner_le_norm (countingDelta x) f

end Singularity
