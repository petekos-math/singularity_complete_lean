import Singularity.CocompactHaarAverages
import Singularity.CompactActionContraction
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Haar-average basins saturated by contracting horocycles

For each bounded continuous observable on the actual compact quotient, there
is one subsequence and a full Haar-measure set on which its averages converge
to the Haar integral. The same limit holds on the entire lower-shear orbit
of every point in that set, with no exceptional shear parameters.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped MatrixGroups UpperHalfPlane Topology BoundedContinuousFunction

namespace Singularity

variable [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
  (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν]

/-- The subsequential Haar basin is saturated along every contracting horocycle. -/
theorem cocompactHaar_lowerShear_average_subsequence (τ : ℝ) (hτ : 0 < τ)
    (f : (SL(2, ℝ) ⧸ Γ) →ᵇ ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂cocompactHaarQuotientProbability Γ ν,
      ∀ u : ℝ, Tendsto
        (fun k => birkhoffAverage ℝ (fun y : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • y)
          f (ns k) (lowerShearMatrix u • x)) atTop
        (𝓝 (∫ y, f y ∂cocompactHaarQuotientProbability Γ ν)) := by
  let := slTwo_polishSpace
  let := cocompact_slTwo_quotient Γ
  obtain ⟨ns, hns, hlim⟩ := cocompactHaar_birkhoffAverage_subsequence Γ ν τ hτ f
    f.continuous.measurable ‖f‖ (norm_nonneg _) f.norm_coe_le_norm
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hlim] with x hx
  intro u
  exact compact_lowerShear_average_limit τ hτ u x f f.continuous
    ns hns.tendsto_atTop _ hx

/-- The same saturated basin has full Haar measure upstairs in SL(2,ℝ). -/
theorem cocompactHaar_group_lowerShear_average_subsequence (τ : ℝ) (hτ : 0 < τ)
    (f : (SL(2, ℝ) ⧸ Γ) →ᵇ ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ g ∂ν, ∀ u : ℝ, Tendsto
      (fun k => birkhoffAverage ℝ (fun y : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • y)
        f (ns k) (lowerShearMatrix u • (QuotientGroup.mk g : SL(2, ℝ) ⧸ Γ))) atTop
      (𝓝 (∫ y, f y ∂cocompactHaarQuotientProbability Γ ν)) := by
  let := slTwo_polishSpace
  let := slTwo_locallyCompactSpace
  let := slTwo_haar_rightInvariant ν
  let : Countable Γ := countable_of_Lindelof_of_discrete
  let := cocompact_slTwo_quotient Γ
  let := cocompactHaarQuotientMeasure_formula Γ ν
  obtain ⟨ns, hns, hlim⟩ := cocompactHaar_birkhoffAverage_subsequence Γ ν τ hτ f
    f.continuous.measurable ‖f‖ (norm_nonneg _) f.norm_coe_le_norm
  have hset : MeasurableSet {x : SL(2, ℝ) ⧸ Γ | Tendsto
      (fun k => birkhoffAverage ℝ (fun y : SL(2, ℝ) ⧸ Γ => dilationMatrix τ • y)
        f (ns k) x) atTop (𝓝 (∫ y, f y ∂cocompactHaarQuotientProbability Γ ν))} := by
    apply measurableSet_tendsto
    intro k
    exact measurable_real_birkhoffAverage _ (measurable_const_smul _) f f.continuous.measurable _
  have hh := (quotientMeasure_ae_iff Γ ν (cocompactHaarQuotientMeasure Γ ν)
    (cocompactHaarDomain_fundamental Γ ν) hset).mpr
    ((cocompactHaarQuotientProbability_measureClass Γ ν).2.ae_le hlim)
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hh] with g hg
  intro u
  exact compact_lowerShear_average_limit τ hτ u _ f f.continuous
    ns hns.tendsto_atTop _ hg

end Singularity
