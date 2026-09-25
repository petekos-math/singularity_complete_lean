import Singularity.VisualShadowFrames
import Singularity.ProjectiveActions
import Singularity.FrameRealBoundaryContinuity

/-!
# Exceptional-point convergence of inverse visual shadows

Compact normalized frames give a convergent subsequence for every sequence
of group elements. Along that subsequence, choosing a sufficiently small cap
parameter puts every late inverse-shadow complement in any prescribed
neighborhood of a single exceptional boundary point.
-/

noncomputable section
open Set Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology

namespace Singularity

/-- Continuity is uniform on a sufficiently small real interval and all
sufficiently late frames of a convergent sequence. -/
theorem smul_small_interval_eventually_subset (a : ℕ → SL(2, ℝ)) (b : SL(2, ℝ))
    (ha : Tendsto a atTop (𝓝 b)) {U : Set (OnePoint ℝ)} (hU : IsOpen U)
    (hb : b • ((0 : ℝ) : OnePoint ℝ) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
      (fun x : ℝ => a n • (x : OnePoint ℝ)) '' Icc (-r) r ⊆ U := by
  have hc := continuous_frame_real_boundary_action
  have hm : (fun p : SL(2, ℝ) × ℝ => p.1 • (p.2 : OnePoint ℝ)) ⁻¹' U ∈ 𝓝 (b, (0 : ℝ)) :=
    hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hb)
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hm
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨ε / 2, by positivity, ?_⟩
  filter_upwards [ha.eventually hV] with n hn
  rintro ξ ⟨x, hx, rfl⟩
  have hxW : x ∈ W := by
    apply he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (abs_le.mpr hx).trans_lt (by linarith)
  exact @hVW (a n, x) ⟨hn, hxW⟩

/-- The inverse visual shadows of any SL₂ sequence have a subsequence with
one exceptional point, in the adjustable-parameter sense. -/
theorem visualShadow_exceptional_subsequence (g : ℕ → SL(2, ℝ)) (z : ℍ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : OnePoint ℝ,
      ∀ U : Set (OnePoint ℝ), IsOpen U → p ∈ U →
        ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
          (((fun ξ : OnePoint ℝ => g (φ n) • ξ) ⁻¹'
            visualShadow z (g (φ n) • z) r)ᶜ) ⊆ U := by
  obtain ⟨b, _, φ, hφ, ht⟩ := inverseVisualShadowFrame_subsequence g z
  refine ⟨φ, hφ, b • ((0 : ℝ) : OnePoint ℝ), fun U hU hp => ?_⟩
  obtain ⟨r, hr, hsub⟩ := smul_small_interval_eventually_subset
    (fun n => inverseVisualShadowFrame (g (φ n)) z) b ht hU hp
  refine ⟨r, hr, ?_⟩
  simpa only [inverse_visualShadow_compl_frame] using hsub

/-- The exceptional-point subsequence statement descends to the actual
projective action, without any choice of lift in its conclusion. -/
theorem projective_visualShadow_exceptional_subsequence (g : ℕ → PSL(2, ℝ)) (z : ℍ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : OnePoint ℝ,
      ∀ U : Set (OnePoint ℝ), IsOpen U → p ∈ U →
        ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
          (((fun ξ : OnePoint ℝ => g (φ n) • ξ) ⁻¹'
            visualShadow z (g (φ n) • z) r)ᶜ) ⊆ U := by
  choose a ha using fun n => slTwoProjective_surjective (g n)
  obtain ⟨φ, hφ, p, hp⟩ := visualShadow_exceptional_subsequence a z
  refine ⟨φ, hφ, p, fun U hU hmem => ?_⟩
  obtain ⟨r, hr, hsub⟩ := hp U hU hmem
  refine ⟨r, hr, ?_⟩
  filter_upwards [hsub] with n hn
  rw [← ha (φ n)]
  exact hn

end Singularity
