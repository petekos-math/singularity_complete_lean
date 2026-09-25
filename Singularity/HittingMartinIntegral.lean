import Singularity.GeometricLastExitConvergence
import Singularity.LastExitExpectation
import Singularity.CompactMartinContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# The Martin density identity for the actual hitting law

Last-exit change of starting point passes to the boundary by dominated
convergence. The uniform Harnack bound on the finite Martin quotients supplies
the domination. Test functions live on the compact ambient sphere.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint BoundedContinuousFunction
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

/-- The actual boundary limits from starts x and 1 satisfy change of measure
with the constructed Martin kernel, tested by bounded continuous sphere functions. -/
theorem geometricBoundaryMap_martin_integral (x : Γ) (φ : OnePoint ℂ →ᵇ ℝ) :
    (∫ ω, φ (compactBoundaryEmbedding
      (x • geometricBoundaryMap Γ s μ hpos hmass hgen hgap UpperHalfPlane.I ω))
      ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass) =
    ∫ ω, (compactMartinPoint Γ s μ hpos hgen hgap horbit
      (geometricBoundaryMap Γ s μ hpos hmass hgen hgap UpperHalfPlane.I ω)).val x *
      φ (compactBoundaryEmbedding
        (geometricBoundaryMap Γ s μ hpos hmass hgen hgap UpperHalfPlane.I ω))
      ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  obtain ⟨A, hA, hexhaust⟩ := exists_finite_exhaustion_containing ({1, x} : Finset Γ)
  have ho (n : ℕ) : 1 ∈ A n := hA n (by simp)
  have hx (n : ℕ) : x ∈ A n := hA n (by simp)
  let V (n : ℕ) := finiteLastExitVertex s (A n) 1 (ho n)
  let W (n : ℕ) := finiteLastExitVertex s (A n) x (hx n)
  let F (n : ℕ) (ω : ℕ → s) := φ (hyperbolicCompactEmbedding (W n ω • UpperHalfPlane.I))
  let T (n : ℕ) (ω : ℕ → s) := martinQuotient s μ 1 x (V n ω) *
    φ (hyperbolicCompactEmbedding (V n ω • UpperHalfPlane.I))
  have hFmeas (n : ℕ) : Measurable (F n) :=
    (measurable_of_countable (fun a : A n => φ (hyperbolicCompactEmbedding (a • UpperHalfPlane.I)))).comp
      (measurable_finiteLastExitVertex s (A n) x (hx n))
  have hTmeas (n : ℕ) : Measurable (T n) :=
    (measurable_of_countable (fun a : A n => martinQuotient s μ 1 x a *
      φ (hyperbolicCompactEmbedding (a • UpperHalfPlane.I)))).comp
      (measurable_finiteLastExitVertex s (A n) 1 (ho n))
  have hF := tendsto_integral_of_dominated_convergence (fun _ : ℕ → s => ‖φ‖)
    (fun n => (hFmeas n).aestronglyMeasurable)
    (integrable_const ‖φ‖ (μ := infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass))
    (fun n => Filter.Eventually.of_forall (fun ω => φ.norm_coe_le_norm _))
    ((geometricLastExitVertex_ae_tendsto Γ s μ hpos hmass hgen hgap A x hx hexhaust
      UpperHalfPlane.I).mono (fun ω hω => φ.continuous.continuousAt.tendsto.comp hω))
  obtain ⟨L, U, hL, hLU⟩ := martinQuotient_bounds s μ hpos hgen hgap 1 x
  have hU : 0 ≤ U := (martinQuotient_pos s μ hpos hgen hgap 1 x 1).le.trans (hLU 1).2
  have hTbound (n : ℕ) (ω : ℕ → s) : ‖T n ω‖ ≤ U * ‖φ‖ := by
    dsimp only [T]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg
      (martinQuotient_pos s μ hpos hgen hgap 1 x (V n ω)).le]
    exact mul_le_mul (hLU _).2 (φ.norm_coe_le_norm _) (norm_nonneg _) hU
  have hTlim := (lastExitMartinQuotient_ae_tendsto Γ s μ hpos hmass hgen hgap horbit
    A ho hexhaust x).and
    (geometricLastExitVertex_ae_tendsto Γ s μ hpos hmass hgen hgap A 1 ho hexhaust UpperHalfPlane.I)
  have hT := tendsto_integral_of_dominated_convergence (fun _ : ℕ → s => U * ‖φ‖)
    (fun n => (hTmeas n).aestronglyMeasurable)
    (integrable_const (U * ‖φ‖) (μ := infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass))
    (fun n => Filter.Eventually.of_forall (hTbound n))
    (hTlim.mono (fun ω hh => by
      simpa only [one_smul, Function.comp_apply, T, V] using hh.1.mul (φ.continuous.continuousAt.tendsto.comp hh.2)))
  have heq (n : ℕ) :
      (∫ ω, F n ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass) =
      ∫ ω, T n ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass :=
    finiteLastExitVertex_change_start s μ hpos hmass hgen hgap (A n) 1 x (ho n) (hx n)
      (fun g => φ (hyperbolicCompactEmbedding (g • UpperHalfPlane.I)))
  exact tendsto_nhds_unique hF (hT.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm)))

end Singularity
