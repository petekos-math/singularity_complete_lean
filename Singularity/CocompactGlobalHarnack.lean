import Singularity.CocompactGreenLower

/-!
# Exponential Green-row comparison from cocompact orbit chains

The same local Harnack constants used for the coarse Green lower bound compare
arbitrary Green rows, with exponential dependence on hyperbolic displacement.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Cocompactness gives an exponential Harnack bound uniform in the target. -/
theorem cocompact_global_greenHarnack (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 ≤ b ∧ ∀ x z y : Γ,
      walkGreen s μ z y ≤ a * Real.exp (b * dist (x • UpperHalfPlane.I) (z • UpperHalfPlane.I)) *
        walkGreen s μ x y := by
  obtain ⟨L, _, hchain⟩ := cocompact_hyperbolic_orbit_chains Γ
  obtain ⟨C, hC, hb⟩ := hyperbolic_uniform_greenHarnack Γ s μ hpos hgen hgap L
  have hp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨Real.exp (7 * Real.log C), 3 * Real.log C,
    Real.one_le_exp_iff.mpr (by positivity), by positivity, ?_⟩
  intro x z y
  obtain ⟨n, f, hf0, hfn, hn, hf⟩ := hchain x z
  have hg := greenHarnack_along_chain Γ s μ C L hp.le hb f n hf y
  rw [hf0, hfn] at hg
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (walkGreen_nonneg s μ (fun g hg => (hpos g hg).le) x y)
  calc
    _ = Real.exp ((n : ℝ) * Real.log C) := by rw [Real.exp_nat_mul, Real.exp_log hp]
    _ ≤ Real.exp ((3 * dist (x • UpperHalfPlane.I) (z • UpperHalfPlane.I) + 7) * Real.log C) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn hlog)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Singularity
