import Singularity.MeasurableKernel
import Singularity.FourierReduction
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# A measurable unit kernel vector for the actual frequency matrix

The Fourier transform is Mathlib's L² Fourier isometry. Its chosen representatives
are strongly measurable. The matrix has N rows and N+1 adjacent frequency samples.
The vector constructed here is measurable on all of ℝ and has Euclidean norm one.
-/

noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Elementwise ComplexConjugate BigOperators

namespace Singularity

/-- Matrix multiplication, bundled continuously in both the matrix and the vector. -/
def euclideanMatrixOperator (m n : ℕ) :
    Matrix (Fin m) (Fin n) ℂ →L[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m)) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap).toContinuousLinearMap

/-- Its coordinate formula is ordinary matrix multiplication. -/
theorem euclideanMatrixOperator_apply (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    euclideanMatrixOperator m n A v j = ∑ l, A j l * v l := rfl

/-- Measurable rectangular matrices have measurable unit kernel vectors. -/
theorem measurable_rectangular_kernel {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (A : Ω → Matrix (Fin N) (Fin (N + 1)) ℂ)
    (hA : ∀ j l, Measurable (fun ω => A ω j l)) :
    ∃ v : Ω → EuclideanSpace ℂ (Fin (N + 1)),
      Measurable v ∧ (∀ ω, ‖v ω‖ = 1) ∧
        (∀ ω j, ∑ l, A ω j l * v ω l = 0) := by
  let : MeasurableSpace
      (EuclideanSpace ℂ (Fin (N + 1)) →L[ℂ] EuclideanSpace ℂ (Fin N)) := borel _
  let : BorelSpace
      (EuclideanSpace ℂ (Fin (N + 1)) →L[ℂ] EuclideanSpace ℂ (Fin N)) := ⟨rfl⟩
  have hAm : Measurable A := Matrix.measurable_iff.mpr hA
  have hB := (euclideanMatrixOperator N (N + 1)).continuous.measurable.comp hAm
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) <
      Module.finrank ℂ (EuclideanSpace ℂ (Fin (N + 1))) := by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    exact Nat.lt_succ_self N
  obtain ⟨v, hv, hvnorm, hvker⟩ := exists_measurable_unit_kernel_of_finrank_lt hdim hB
  refine ⟨v, hv, hvnorm, ?_⟩
  intro ω j
  have h := congrArg (fun z : EuclideanSpace ℂ (Fin N) => z j) (hvker ω)
  exact h

/-- N × (N+1) matrix of conjugated frequency samples. In Mathlib's Fourier
convention the lattice spacing for translates by τ will be `q = 1/τ`. -/
def frequencyMatrix {N : ℕ} (k : Fin N → RealLineL2) (q : ℝ) (ω : ℝ) :
    Matrix (Fin N) (Fin (N + 1)) ℂ :=
  fun j l => conj ((Lp.fourierTransformₗᵢ ℝ ℂ (k j) : ℝ → ℂ) (ω + (l : ℕ) * q))

/-- The actual frequency-matrix entries are measurable. -/
theorem frequencyMatrix_measurable {N : ℕ} (k : Fin N → RealLineL2) (q : ℝ)
    (j : Fin N) (l : Fin (N + 1)) : Measurable (fun ω => frequencyMatrix k q ω j l) := by
  have h := (Lp.stronglyMeasurable (Lp.fourierTransformₗᵢ ℝ ℂ (k j))).measurable
  have hs : Measurable (fun ω : ℝ => ω + (l : ℕ) * q) :=
    measurable_id.add measurable_const
  exact Complex.continuous_conj.measurable.comp (h.comp hs)

/-- The measurable frequency vector required by the finite-band construction.
No measurable-selection hypothesis is left to assume. -/
theorem exists_frequency_unit_kernel {N : ℕ} (k : Fin N → RealLineL2) (q : ℝ) :
    ∃ v : ℝ → EuclideanSpace ℂ (Fin (N + 1)),
      Measurable v ∧ (∀ ω, ‖v ω‖ = 1) ∧
        (∀ ω j, ∑ l : Fin (N + 1), conj ((Lp.fourierTransformₗᵢ ℝ ℂ (k j) : ℝ → ℂ)
          (ω + (l : ℕ) * q)) * v ω l = 0) :=
  measurable_rectangular_kernel (frequencyMatrix k q) (frequencyMatrix_measurable k q)

end Singularity
