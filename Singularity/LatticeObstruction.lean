import Singularity.BandOrthogonality
import Singularity.FourierTranslation

/-!
# Finitely many lattice-translate families cannot span L²(ℝ)

For any finite family of complex L² functions and positive lattice spacing, this
module constructs a nonzero L² function orthogonal to every lattice translate.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators

namespace Singularity

/-- Passing the integrated frequency cancellation back through the L² Fourier
isometry gives orthogonality in the original variable. -/
theorem finiteBand_inverse_orthogonal {N : ℕ} (k : Fin N → RealLineL2)
    {q : ℝ} (hq : 0 < q)
    {v : ℝ → EuclideanSpace ℂ (Fin (N + 1))} (hv : Measurable v)
    (hnorm : ∀ ω, ‖v ω‖ = 1)
    (hker : ∀ ω j, ∑ l : Fin (N + 1), frequencyMatrix k q ω j l * v ω l = 0)
    (n : ℤ) (j : Fin N) :
    inner ℂ (realTranslation ((n : ℝ) / q) (k j))
      ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (finiteBandL2 q hv hnorm)) = 0 := by
  rw [← (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map,
    fourier_realTranslation, LinearIsometryEquiv.apply_symm_apply, L2.inner_def]
  have hband : (finiteBandL2 q hv hnorm : ℝ → ℂ) =ᵐ[volume] finiteBand q v :=
    MemLp.coeFn_toLp _
  calc
    ∫ t, inner ℂ (frequencyModulation ((n : ℝ) / q)
        (Lp.fourierTransformₗᵢ ℝ ℂ (k j)) t) (finiteBandL2 q hv hnorm t) =
        ∫ t, (conj (translationPhase ((n : ℝ) / q) t) *
          conj ((Lp.fourierTransformₗᵢ ℝ ℂ (k j) : ℝ → ℂ) t)) * finiteBand q v t := by
      apply integral_congr_ae
      filter_upwards [frequencyModulation_apply_ae ((n : ℝ) / q)
        (Lp.fourierTransformₗᵢ ℝ ℂ (k j)), hband] with t ht hb
      rw [ht, hb]
      simp [RCLike.inner_apply, map_mul, mul_comm]
    _ = 0 := frequency_kernel_pairing_zero k q hv hnorm hker j
      (Complex.continuous_conj.measurable.comp (translationPhase_continuous _).measurable)
      (fun t => by simp [translationPhase_norm])
      (fun ω l => congrArg conj (translationPhase_lattice hq.ne' n l ω))

/-- Every finite family of L² functions has a nonzero vector orthogonal to all
of its translates by a fixed positive lattice. -/
theorem exists_orthogonal_lattice_translates {N : ℕ} (k : Fin N → RealLineL2)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ φ : RealLineL2, φ ≠ 0 ∧
      ∀ (n : ℤ) (j : Fin N), inner ℂ (realTranslation ((n : ℝ) * τ) (k j)) φ = 0 := by
  let q := τ⁻¹
  have hq : 0 < q := inv_pos.mpr hτ
  obtain ⟨v, hv, hnorm, hker⟩ := exists_frequency_unit_kernel k q
  refine ⟨(Lp.fourierTransformₗᵢ ℝ ℂ).symm (finiteBandL2 q hv hnorm), ?_, ?_⟩
  · intro hzero
    have h := congrArg (Lp.fourierTransformₗᵢ ℝ ℂ) hzero
    simp only [LinearIsometryEquiv.apply_symm_apply, map_zero] at h
    exact finiteBandL2_ne_zero hq hv hnorm h
  · intro n j
    have h := finiteBand_inverse_orthogonal k hq hv hnorm hker n j
    simpa only [q, div_inv_eq_mul] using h

/-- The same obstruction for an arbitrary finite indexing type. -/
theorem exists_orthogonal_lattice_translates_fintype {J : Type*} [Fintype J]
    (k : J → RealLineL2) {τ : ℝ} (hτ : 0 < τ) :
    ∃ φ : RealLineL2, φ ≠ 0 ∧
      ∀ (n : ℤ) (j : J), inner ℂ (realTranslation ((n : ℝ) * τ) (k j)) φ = 0 := by
  classical
  let e := Fintype.equivFin J
  obtain ⟨φ, hφ, ho⟩ := exists_orthogonal_lattice_translates (fun j => k (e.symm j)) hτ
  exact ⟨φ, hφ, fun n j => by simpa using ho n (e j)⟩

/-- The closed linear span of the translates is a proper subspace of L². -/
theorem lattice_translates_closed_span_ne_top {J : Type*} [Fintype J]
    (k : J → RealLineL2) {τ : ℝ} (hτ : 0 < τ) :
    (Submodule.span ℂ (Set.range (fun p : ℤ × J =>
      realTranslation ((p.1 : ℝ) * τ) (k p.2)))).topologicalClosure ≠ ⊤ := by
  obtain ⟨φ, hφ, ho⟩ := exists_orthogonal_lattice_translates_fintype k hτ
  let S := Submodule.span ℂ (Set.range (fun p : ℤ × J =>
    realTranslation ((p.1 : ℝ) * τ) (k p.2)))
  have hs : S ≤ (innerSL ℂ φ).ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨n, j⟩, rfl⟩
    exact inner_eq_zero_symm.mpr (ho n j)
  have hc := S.topologicalClosure_minimal hs (innerSL ℂ φ).isClosed_ker
  intro htop
  change S.topologicalClosure = ⊤ at htop
  rw [htop] at hc
  have hzero : inner ℂ φ φ = 0 := hc Submodule.mem_top
  exact hφ (inner_self_eq_zero.mp hzero)

end Singularity
