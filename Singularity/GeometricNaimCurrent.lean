import Singularity.GeometricNaimCovariance
import Singularity.HittingMartinIdentification
import Singularity.GeometricKernelCurrent

/-!
# The invariant Naïm current of the actual hitting measures

The constructed positive continuous global kernel weights the actual backward
and forward hitting laws. Its Martin covariance and the proved derivative
identification discharge the invariance hypothesis. No absolute continuity
with respect to visual measure is required for this construction.
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
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)

local notation "νm" => reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z
local notation "νp" => geometricHittingMeasure Γ s μ hpos hmass hgen hgap z
local notation "Θ" => geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞)
local notation "Km" => compactMartinPoint Γ (s.map (Function.Embedding.mk Inv.inv inv_injective))
  (fun g => μ g⁻¹) (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
  (reflectedMarkov_spectral_gap s μ hgap) (horbit ∞)
local notation "Kp" => compactMartinPoint Γ s μ hpos hgen hgap (horbit ∞)

/-- The global kernel has covariance in the actual hitting Radon--Nikodym derivatives. -/
theorem geometricNaimKernel_density_covariance (g : Γ) :
    ∀ᵐ p ∂geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z,
      Θ (g⁻¹ • p) = Θ p /
        (stationaryRealDensity νm g p.val.1 * stationaryRealDensity νp g p.val.2) := by
  let : IsProbabilityMeasure νm := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  let : IsProbabilityMeasure νp := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  let : NullSingletonClass νp := geometricHittingMeasure_nullSingleton Γ s μ hpos hmass hgen hgap z horbit
  have hm := geometricHittingMeasure_realDensity_eq_martin_all Γ
    (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹)
    (reflected_jump_pos s μ hpos) ((reflected_jump_mass s μ).trans hmass)
    (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap) (horbit ∞) z
  have hp := geometricHittingMeasure_realDensity_eq_martin_all Γ s μ hpos hmass hgen hgap (horbit ∞) z
  have hm' : ∀ᵐ p ∂(νm).prod νp, stationaryRealDensity νm g p.1 = (Km p.1).val g :=
    Measure.quasiMeasurePreserving_fst.ae (hm.mono (fun _ h => h g))
  have hp' : ∀ᵐ p ∂(νm).prod νp, stationaryRealDensity νp g p.2 = (Kp p.2).val g :=
    Measure.quasiMeasurePreserving_snd.ae (hp.mono (fun _ h => h g))
  have hpair := hm'.and hp'
  rw [← boundaryPairMeasure_map_eq νm νp, measurableEmbedding_boundaryPair.ae_map_iff] at hpair
  filter_upwards [hpair] with p hp
  rw [hp.1, hp.2]
  have he : ((g⁻¹ : Γ) : SL(2, ℝ)) • p = g⁻¹ • p := by
    apply Subtype.ext
    rfl
  have hc := geometricNaimKernel_smul Γ s μ hpos hmass hgen hgap (horbit ∞) g⁻¹ p
  rw [he] at hc
  simpa only [inv_inv] using hc

/-- The actual Naïm current on the off-diagonal compact boundary. -/
def geometricNaimCurrent : Measure BoundaryPair :=
  geometricKernelCurrent Γ s μ hpos hmass hgen hgap z Θ

theorem geometricNaimCurrent_sigmaFinite :
    SigmaFinite (geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z) :=
  geometricKernelCurrent_sigmaFinite Γ s μ hpos hmass hgen hgap z Θ

theorem geometricNaimCurrent_locallyFinite :
    IsLocallyFiniteMeasure (geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z) :=
  geometricKernelCurrent_locallyFinite Γ s μ hpos hmass hgen hgap z Θ
    (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞))

theorem geometricNaimCurrent_regular :
    Measure.Regular (geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z) :=
  geometricKernelCurrent_regular Γ s μ hpos hmass hgen hgap z Θ
    (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞))

theorem geometricNaimCurrent_ne_zero :
    geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z ≠ 0 :=
  geometricKernelCurrent_ne_zero Γ s μ hpos hmass hgen hgap z horbit Θ
    (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞)).measurable
    (geometricNaimKernel_pos Γ s μ hpos hmass hgen hgap (horbit ∞))

/-- The actual Naïm current is invariant under every group element. -/
theorem geometricNaimCurrent_invariant (g : Γ) :
    Measure.map (fun p : BoundaryPair => g • p)
      (geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z) =
      geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z :=
  geometricKernelCurrent_invariant Γ s μ hpos hmass hgen hgap z horbit Θ
    (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞)).measurable g
    (geometricNaimKernel_density_covariance Γ s μ hpos hmass hgen hgap horbit z g)

/-- The actual current has precisely the backward-forward hitting product measure class. -/
theorem geometricNaimCurrent_measureClass :
    geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z ≪
      geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z ∧
    geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z ≪
      geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z :=
  boundaryPairCurrent_measureClass νm νp Θ
    (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞)).measurable
    (geometricNaimKernel_pos Γ s μ hpos hmass hgen hgap (horbit ∞))

end Singularity
