import Singularity.HyperbolicHarnack
import Singularity.CocompactOrbitChains

/-!
# A coarse exponential Green lower bound

Cocompactness supplies short orbit chains, and discreteness turns the local
path Harnack constants into a uniform constant. Iteration gives an exponential
lower bound for the actual Green kernel. The exponent is not asserted to be one.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A chain of N locally comparable vertices gives the lower bound C^(-N). -/
theorem walkGreen_lower_of_harnack_chain (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (C L : ℝ) (hC : 0 < C)
    (hb : ∀ x z y : Γ, dist (x • UpperHalfPlane.I) (z • UpperHalfPlane.I) ≤ L →
      walkGreen s μ z y ≤ C * walkGreen s μ x y)
    (f : ℕ → Γ) (n : ℕ)
    (hf : ∀ k < n, dist (f k • UpperHalfPlane.I) (f (k + 1) • UpperHalfPlane.I) ≤ L) :
    Real.exp (-(n : ℝ) * Real.log C) ≤ walkGreen s μ (f 0) (f n) := by
  have hh := (walkGreen_diag_ge_one s μ hμ hgap (f n)).trans
    (greenHarnack_along_chain Γ s μ C L hC.le hb f n hf (f n))
  have he : Real.exp (-(n : ℝ) * Real.log C) = 1 / C ^ n := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hC, one_div]
  rw [he]
  apply (div_le_iff₀ (pow_pos hC n)).mpr
  simpa only [mul_comm] using hh

/-- Every positive semigroup-generating finite law with a spectral gap on a
discrete cocompact group has a coarse exponential Green lower bound. -/
theorem cocompact_walkGreen_exp_lower (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x y : Γ,
      a * Real.exp (-b * dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) ≤ walkGreen s μ x y := by
  obtain ⟨L, _, hchain⟩ := cocompact_hyperbolic_orbit_chains Γ
  obtain ⟨C, hC, hb⟩ := hyperbolic_uniform_greenHarnack Γ s μ hpos hgen hgap L
  have hp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨Real.exp (-7 * Real.log C), 3 * Real.log C + 1, Real.exp_pos _, by positivity, ?_⟩
  intro x y
  obtain ⟨n, f, hf0, hfn, hn, hf⟩ := hchain x y
  have hg := walkGreen_lower_of_harnack_chain Γ s μ (fun g hg => (hpos g hg).le)
    hgap C L hp hb f n hf
  rw [hf0, hfn] at hg
  apply le_trans _ hg
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hn hlog
  nlinarith [dist_nonneg (x := x • UpperHalfPlane.I) (y := y • UpperHalfPlane.I)]

end Singularity
