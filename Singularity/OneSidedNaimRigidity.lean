import Singularity.StableFrameMeasureTransfer
import Singularity.NaimQuotientComparison
import Singularity.CocompactStableAverages

/-!
# One-sided rigidity of the actual Naïm quotient probability

Visual absolute continuity of the forward hitting law suffices. The backward
law remains arbitrary in the stable-product transfer. Haar average basins
transfer to the actual finite invariant Naïm probability, forcing equality
of integrals of every continuous observable and hence equality of measures.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set OnePoint
open scoped MatrixGroups UpperHalfPlane Topology

namespace Singularity

attribute [local instance] slTwo_polishSpace slTwo_locallyCompactSpace cocompact_slTwo_quotient

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
  (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)
  (ρ : Measure SL(2, ℝ)) [IsHaarMeasure ρ]

set_option maxHeartbeats 1200000 in
/-- Forward visual absolute continuity identifies the actual Naïm quotient with Haar. -/
theorem geometricNaimQuotientProbability_eq_haar_of_forward_ac
    (hac : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪
      compactPoissonMeasure UpperHalfPlane.I) :
    geometricNaimQuotientProbability Γ s μ hpos hmass hgen hgap horbit z =
      cocompactHaarQuotientProbability Γ ρ := by
  let := geometricNaimQuotientProbability_probability Γ s μ hpos hmass hgen hgap horbit z
  let := cocompactHaarQuotientProbability_probability Γ ρ
  let := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  let := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  let := geometricHittingMeasure_nullSingleton Γ s μ hpos hmass hgen hgap z horbit
  let := geometricNaimCurrent_sigmaFinite Γ s μ hpos hmass hgen hgap horbit z
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  obtain ⟨ns, hns, hlim⟩ := cocompactHaar_group_lowerShear_average_subsequence Γ ρ 1 (by norm_num) f
  let T : (SL(2, ℝ) ⧸ Γ) → (SL(2, ℝ) ⧸ Γ) := fun x => dilationMatrix 1 • x
  let c : ℝ := ∫ x, f x ∂cocompactHaarQuotientProbability Γ ρ
  let P : (SL(2, ℝ) ⧸ Γ) → Prop := fun x =>
    Tendsto (fun k => birkhoffAverage ℝ T f (ns k) x) atTop (𝓝 c)
  have hP : MeasurableSet {x | P x} :=
    measurableSet_tendsto _ (fun k => measurable_real_birkhoffAverage T
      (measurable_const_smul _) f f.continuous.measurable (ns k))
  have hπ : Measurable (QuotientGroup.mk : SL(2, ℝ) → SL(2, ℝ) ⧸ Γ) :=
    measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  have href : ∀ᵐ g ∂ρ, P (QuotientGroup.mk g) := by
    filter_upwards [hlim] with g hg
    simpa only [lowerShearMatrix_zero, one_smul] using hg 0
  have hframe : ∀ᵐ g ∂geometricNaimFrameMeasure Γ s μ hpos hmass hgen hgap horbit z,
      P (QuotientGroup.mk g) := by
    apply ae_currentFrameLift_of_forward_ac ρ
      (reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z)
      (geometricHittingMeasure Γ s μ hpos hmass hgen hgap z) _
      (geometricNaimCurrent_measureClass Γ s μ hpos hmass hgen hgap horbit z).1 hac
      (fun g => P (QuotientGroup.mk g)) (hP.preimage hπ)
    · intro u g hg
      change P (lowerShearMatrix u • (QuotientGroup.mk g : SL(2, ℝ) ⧸ Γ))
      exact compact_lowerShear_average_limit 1 (by norm_num) u
        (QuotientGroup.mk g : SL(2, ℝ) ⧸ Γ) f f.continuous
        ns hns.tendsto_atTop c hg
    · exact href
  have hquot : ∀ᵐ x ∂geometricNaimQuotientMeasure Γ s μ hpos hmass hgen hgap horbit z, P x := by
    exact (ae_map_iff hπ.aemeasurable hP).mpr (ae_restrict_of_ae hframe)
  have hprob := (geometricNaimQuotientProbability_measureClass Γ s μ hpos hmass hgen hgap horbit z).1.ae_le hquot
  exact integral_eq_of_birkhoffAverage_subsequence _ T
    (geometricNaimQuotientProbability_dilation_invariant Γ s μ hpos hmass hgen hgap horbit z 1)
    f f.continuous.measurable ‖f‖ (norm_nonneg _) f.norm_coe_le_norm
    ns hns.tendsto_atTop c hprob

include horbit ρ in
/-- One-sided visual absolute continuity also forces it for the reflected hitting law. -/
theorem reflectedGeometricHittingMeasure_ac_visual_of_forward_ac
    (hac : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪
      compactPoissonMeasure UpperHalfPlane.I) :
    reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≪
      compactPoissonMeasure UpperHalfPlane.I := by
  apply (geometricHittingMeasures_ac_visual_of_quotient_ac Γ s μ hpos hmass hgen hgap horbit z ρ ?_).1
  rw [geometricNaimQuotientProbability_eq_haar_of_forward_ac Γ s μ hpos hmass hgen hgap horbit z ρ hac]

end Singularity
