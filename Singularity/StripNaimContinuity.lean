import Singularity.StripNaimKernel

/-!
# Joint continuity of the Naïm kernel on opposite boundary sides

The full arbitrary-approach quotient limit gives joint continuity by diagonal
orbit approximations. This is proved directly on the negative-positive chart;
global chart construction and covariance remain separate steps.
-/

noncomputable section
open Filter Set
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- Ordered finite endpoints lying on opposite sides of the strip. -/
@[reducible]
def oppositeBoundaryPairs := {p : ℝ × ℝ // p.1 < 0 ∧ 0 < p.2}

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

/-- The actual Naïm quotient limit is jointly continuous on the opposite-side chart. -/
theorem continuous_stripNaimKernel :
    Continuous (fun p : oppositeBoundaryPairs =>
      stripNaimKernel Γ s μ hpos hmass hgen hgap p.val.1 p.val.2 p.property.1.ne p.property.2.ne') := by
  apply continuous_iff_seqContinuous.mpr
  intro p q hp
  let T := fun r : oppositeBoundaryPairs =>
    stripNaimKernel Γ s μ hpos hmass hgen hgap r.val.1 r.val.2 r.property.1.ne r.property.2.ne'
  have hchoose (n : ℕ) : ∃ k : ℕ,
      dist (((cocompactRaySequence Γ (p n).val.1 k) • UpperHalfPlane.I : ℍ) : ℂ) ((p n).val.1 : ℂ) <
        1 / ((n : ℝ) + 1) ∧
      dist (((cocompactRaySequence Γ (p n).val.2 k) • UpperHalfPlane.I : ℍ) : ℂ) ((p n).val.2 : ℂ) <
        1 / ((n : ℝ) + 1) ∧
      dist (finiteNaimQuotient s μ 1 (cocompactRaySequence Γ (p n).val.1 k)
        (cocompactRaySequence Γ (p n).val.2 k)) (T (p n)) < 1 / ((n : ℝ) + 1) := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hx := (cocompactRaySequence_tendsto Γ (p n).val.1).eventually (Metric.ball_mem_nhds _ hε)
    have hy := (cocompactRaySequence_tendsto Γ (p n).val.2).eventually (Metric.ball_mem_nhds _ hε)
    have hθ := (stripNaimKernel_tendsto Γ s μ hpos hmass hgen hgap (p n).property.1 (p n).property.2
      (cocompactRaySequence Γ (p n).val.1) (cocompactRaySequence Γ (p n).val.2)
      (cocompactRaySequence_tendsto Γ (p n).val.1) (cocompactRaySequence_tendsto Γ (p n).val.2)).eventually
      (Metric.ball_mem_nhds _ hε)
    exact (hx.and (hy.and hθ)).exists
  choose k hkx hky hkθ using hchoose
  let x : ℕ → Γ := fun n => cocompactRaySequence Γ (p n).val.1 (k n)
  let y : ℕ → Γ := fun n => cocompactRaySequence Γ (p n).val.2 (k n)
  have hpx : Tendsto (fun n => (p n).val.1) atTop (𝓝 q.val.1) :=
    (continuous_fst.comp continuous_subtype_val).continuousAt.tendsto.comp hp
  have hpy : Tendsto (fun n => (p n).val.2) atTop (𝓝 q.val.2) :=
    (continuous_snd.comp continuous_subtype_val).continuousAt.tendsto.comp hp
  have hdx : Tendsto (fun n => dist ((p n).val.1 : ℂ) ((x n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [dist_comm]
    exact (hkx n).le
  have hdy : Tendsto (fun n => dist ((p n).val.2 : ℂ) ((y n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [dist_comm]
    exact (hky n).le
  have hx := (Complex.continuous_ofReal.continuousAt.tendsto.comp hpx).congr_dist hdx
  have hy := (Complex.continuous_ofReal.continuousAt.tendsto.comp hpy).congr_dist hdy
  have ht := stripNaimKernel_tendsto Γ s μ hpos hmass hgen hgap q.property.1 q.property.2 x y hx hy
  apply ht.congr_dist
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hkθ n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end Singularity
