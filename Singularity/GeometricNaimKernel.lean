import Singularity.TransverseMartinVectors
import Singularity.StripNaimKernel

/-!
# The Naïm kernel on the entire off-diagonal geometric boundary

An ambient chart puts any ordered distinct endpoints on opposite sides of a
moved strip. Ordinary Ancona gives strong Martin-vector limits on that strip.
The exact separator pairing then gives one finite real limit for every pair
of approaches. Uniqueness makes this construction independent of the chart.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

include hpos hmass hgen hgap horbit in
/-- Every ordered distinct pair has one Naïm limit along all orbit approaches. -/
theorem exists_geometricNaimKernel_limit (p : BoundaryPair) :
    ∃ θ : ℝ, ∀ x y : ℕ → Γ,
      Tendsto (fun n => hyperbolicCompactEmbedding (x n • UpperHalfPlane.I)) atTop
        (𝓝 (compactBoundaryEmbedding p.val.1)) →
      Tendsto (fun n => hyperbolicCompactEmbedding (y n • UpperHalfPlane.I)) atTop
        (𝓝 (compactBoundaryEmbedding p.val.2)) →
      Tendsto (fun n => finiteNaimQuotient s μ 1 (x n) (y n)) atTop (𝓝 θ) := by
  obtain ⟨B, hB₁, hB₂⟩ := exists_opposite_boundary_chart p
  let A := transverseJumpStrip Γ s B
  let M := (walkGreenCompression s μ (fun g hg => (hpos g hg).le) hmass hgap A).symm
  obtain ⟨x₀, hx₀⟩ := exists_compact_boundary_orbit_approach Γ horbit p.val.1
  obtain ⟨y₀, hy₀⟩ := exists_compact_boundary_orbit_approach Γ horbit p.val.2
  obtain ⟨u, _, hu, _, _, _⟩ := transverseMartinVectors_limit Γ s μ hpos hmass hgen hgap horbit
    B p.val.1 (-1) (by norm_num) hB₁ x₀ hx₀
  obtain ⟨_, v, _, hv, _, _⟩ := transverseMartinVectors_limit Γ s μ hpos hmass hgen hgap horbit
    B p.val.2 1 one_ne_zero hB₂ y₀ hy₀
  refine ⟨(inner ℂ u (M v)).re, ?_⟩
  intro x y hx hy
  obtain ⟨u', _, hu', _, hut, _⟩ := transverseMartinVectors_limit Γ s μ hpos hmass hgen hgap horbit
    B p.val.1 (-1) (by norm_num) hB₁ x hx
  obtain ⟨_, v', _, hv', _, hvt⟩ := transverseMartinVectors_limit Γ s μ hpos hmass hgen hgap horbit
    B p.val.2 1 one_ne_zero hB₂ y hy
  have hue : u' = u := supportedL2_ext_on A u' u (fun g hg => (hu' g hg).trans (hu g hg).symm)
  have hve : v' = v := supportedL2_ext_on A v' v (fun g hg => (hv' g hg).trans (hv g hg).symm)
  rw [hue] at hut
  rw [hve] at hvt
  have hp := pairing_tendsto M.toContinuousLinearMap hut hvt
  have hxB := compact_approach_in_chart B p.val.1 (-1) hB₁ (fun n => x n • UpperHalfPlane.I) hx
  have hyB := compact_approach_in_chart B p.val.2 1 hB₂ (fun n => y n • UpperHalfPlane.I) hy
  have hxr : Tendsto (fun n => (B • (x n • UpperHalfPlane.I)).re) atTop (𝓝 (-1 : ℝ)) :=
    Complex.continuous_re.continuousAt.tendsto.comp hxB
  have hyr : Tendsto (fun n => (B • (y n • UpperHalfPlane.I)).re) atTop (𝓝 (1 : ℝ)) :=
    Complex.continuous_re.continuousAt.tendsto.comp hyB
  have he : ∀ᶠ n in atTop,
      inner ℂ (normalizedGreenRow s μ A (x n) (walkGreen s μ (x n) 1))
        (M (normalizedGreenColumn s μ A (y n) (walkGreen s μ 1 (y n)))) =
        (finiteNaimQuotient s μ 1 (x n) (y n) : ℂ) := by
    filter_upwards [hxr.eventually (gt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)),
      hyr.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn hm
    have h := normalizedGreen_separator_pairing s μ (fun g hg => (hpos g hg).le) hmass hgap A
      (x n) (y n) (walkGreen s μ (x n) 1) (walkGreen s μ 1 (y n))
      (transverseJumpStrip_separates Γ s B (x n) (y n) hn hm.le)
    simpa only [finiteNaimQuotient, Complex.ofReal_div, Complex.ofReal_mul] using h.symm
  have ht : Tendsto (fun n => (finiteNaimQuotient s μ 1 (x n) (y n) : ℂ)) atTop
      (𝓝 (inner ℂ u (M v))) := by
    simpa only [ContinuousLinearEquiv.coe_coe] using hp.congr' he
  simpa only [Function.comp_def, Complex.ofReal_re] using
    Complex.continuous_re.continuousAt.tendsto.comp ht

/-- The actual Naïm kernel on ordered distinct compact geometric boundary points. -/
def geometricNaimKernel (p : BoundaryPair) : ℝ :=
  (exists_geometricNaimKernel_limit Γ s μ hpos hmass hgen hgap horbit p).choose

/-- Full two-variable approach convergence, including endpoints at infinity. -/
theorem geometricNaimKernel_tendsto (p : BoundaryPair) (x y : ℕ → Γ)
    (hx : Tendsto (fun n => hyperbolicCompactEmbedding (x n • UpperHalfPlane.I)) atTop
      (𝓝 (compactBoundaryEmbedding p.val.1)))
    (hy : Tendsto (fun n => hyperbolicCompactEmbedding (y n • UpperHalfPlane.I)) atTop
      (𝓝 (compactBoundaryEmbedding p.val.2))) :
    Tendsto (fun n => finiteNaimQuotient s μ 1 (x n) (y n)) atTop
      (𝓝 (geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit p)) :=
  (exists_geometricNaimKernel_limit Γ s μ hpos hmass hgen hgap horbit p).choose_spec x y hx hy

/-- The global kernel retains the universal positive Green lower bound. -/
theorem geometricNaimKernel_lower (p : BoundaryPair) :
    (walkGreen s μ 1 1)⁻¹ ≤ geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit p := by
  obtain ⟨x, hx⟩ := exists_compact_boundary_orbit_approach Γ horbit p.val.1
  obtain ⟨y, hy⟩ := exists_compact_boundary_orbit_approach Γ horbit p.val.2
  apply ge_of_tendsto (geometricNaimKernel_tendsto Γ s μ hpos hmass hgen hgap horbit p x y hx hy)
  exact Eventually.of_forall (fun n => finiteNaimQuotient_lower s μ hpos hmass hgen hgap 1 (x n) (y n))

theorem geometricNaimKernel_pos (p : BoundaryPair) :
    0 < geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit p :=
  (inv_pos.mpr (walkGreen_pos s μ hpos hgen hgap 1 1)).trans_le
    (geometricNaimKernel_lower Γ s μ hpos hmass hgen hgap horbit p)

/-- The global construction agrees with the original opposite-side strip kernel. -/
theorem geometricNaimKernel_eq_strip {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η) :
    geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit
      ⟨((ξ : OnePoint ℝ), (η : OnePoint ℝ)), fun h => (ne_of_lt (hξ.trans hη)) (OnePoint.coe_injective h)⟩ =
      stripNaimKernel Γ s μ hpos hmass hgen hgap ξ η hξ.ne hη.ne' := by
  let p : BoundaryPair := ⟨((ξ : OnePoint ℝ), (η : OnePoint ℝ)),
    fun h => (ne_of_lt (hξ.trans hη)) (OnePoint.coe_injective h)⟩
  exact tendsto_nhds_unique
    (geometricNaimKernel_tendsto Γ s μ hpos hmass hgen hgap horbit p
      (cocompactRaySequence Γ ξ) (cocompactRaySequence Γ η)
      (OnePoint.continuous_coe.continuousAt.tendsto.comp (cocompactRaySequence_tendsto Γ ξ))
      (OnePoint.continuous_coe.continuousAt.tendsto.comp (cocompactRaySequence_tendsto Γ η)))
    (stripNaimKernel_tendsto Γ s μ hpos hmass hgen hgap hξ hη
      (cocompactRaySequence Γ ξ) (cocompactRaySequence Γ η)
      (cocompactRaySequence_tendsto Γ ξ) (cocompactRaySequence_tendsto Γ η))

end Singularity
