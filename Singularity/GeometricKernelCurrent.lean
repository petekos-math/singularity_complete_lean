import Singularity.BoundaryPairInvariance

/-!
# Kernel currents over the actual forward and reflected hitting laws

Both marginals are the already constructed random-walk hitting measures.
Reflection inherits its spectral gap, probability normalization, and semigroup
generation. A real kernel weights their product on distinct endpoints. This
constructs a candidate geometric current, not the still-unproved Naïm kernel.
Continuity, positivity, and covariance are explicit inputs where needed.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ)
  (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)

/-- The reflected marginal is the hitting law of the actual reflected walk. -/
def reflectedGeometricHittingMeasure : Measure (OnePoint ℝ) :=
  geometricHittingMeasure Γ (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflected_jump_pos s μ hpos) ((reflected_jump_mass s μ).trans hmass)
    (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap) z

local notation "νm" => reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z
local notation "νp" => geometricHittingMeasure Γ s μ hpos hmass hgen hgap z

theorem reflectedGeometricHittingMeasure_probability : IsProbabilityMeasure νm :=
  geometricHittingMeasure_probability Γ _ _ _ _ _ _ z

theorem reflectedGeometricHittingMeasure_stationary :
    νm = ∑ g : s.map ⟨Inv.inv, inv_injective⟩,
      ENNReal.ofReal (μ (g : Γ)⁻¹) • Measure.map (fun p : OnePoint ℝ => (g : Γ) • p) νm :=
  geometricHittingMeasure_stationary Γ _ _ _ _ _ _ z

/-- The reference measure consists of an independent backward and forward endpoint. -/
def geometricBoundaryPairMeasure : Measure BoundaryPair := boundaryPairMeasure νm νp

/-- A kernel on distinct geometric endpoints weights the actual two hitting laws. -/
def geometricKernelCurrent (K : BoundaryPair → ℝ) : Measure BoundaryPair :=
  boundaryPairCurrent νm νp K

theorem geometricKernelCurrent_sigmaFinite (K : BoundaryPair → ℝ) :
    SigmaFinite (geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K) := by
  have := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact boundaryPairCurrent_sigmaFinite _ _ K

/-- A continuous off-diagonal kernel gives a locally finite geometric current. -/
theorem geometricKernelCurrent_locallyFinite (K : BoundaryPair → ℝ) (hK : Continuous K) :
    IsLocallyFiniteMeasure (geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K) := by
  have := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact boundaryPairCurrent_locallyFinite _ _ K hK

theorem geometricKernelCurrent_regular (K : BoundaryPair → ℝ) (hK : Continuous K) :
    Measure.Regular (geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K) := by
  have := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact boundaryPairCurrent_regular _ _ K hK

/-- The two marginal absolute-continuity conclusions of rigidity imply current comparison. -/
theorem geometricKernelCurrent_absolutelyContinuous (m : Measure (OnePoint ℝ)) [SFinite m]
    (hback : νm ≪ m) (hforward : νp ≪ m) (K L : BoundaryPair → ℝ)
    (hL : Measurable L) (hpL : ∀ p, 0 < L p) :
    geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K ≪ boundaryPairCurrent m m L := by
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  exact boundaryPairCurrent_absolutelyContinuous νm m νp m hback hforward K L hL hpL

variable (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)
include horbit

/-- Distinctness removes a null set from the actual backward-forward endpoint law. -/
theorem geometricBoundaryPairMeasure_probability :
    IsProbabilityMeasure (geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z) := by
  have := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_nullSingleton Γ s μ hpos hmass hgen hgap z horbit
  exact boundaryPairMeasure_probability _ _

/-- Positivity of the kernel gives nonzero mass without assuming absolute continuity. -/
theorem geometricKernelCurrent_ne_zero (K : BoundaryPair → ℝ) (hK : Measurable K) (hp : ∀ p, 0 < K p) :
    geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K ≠ 0 := by
  have := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_nullSingleton Γ s μ hpos hmass hgen hgap z horbit
  exact boundaryPairCurrent_ne_zero _ _ K hK hp

/-- The actual hitting-law current is invariant once its kernel satisfies covariance
in the actual hitting derivatives. Martin identification is not silently assumed. -/
theorem geometricKernelCurrent_invariant (K : BoundaryPair → ℝ) (hK : Measurable K) (g : Γ)
    (hc : ∀ᵐ p ∂geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z,
      K (g⁻¹ • p) = K p / (stationaryRealDensity νm g p.val.1 * stationaryRealDensity νp g p.val.2)) :
    Measure.map (fun p : BoundaryPair => g • p) (geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K) =
      geometricKernelCurrent Γ s μ hpos hmass hgen hgap z K := by
  have := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_nullSingleton Γ s μ hpos hmass hgen hgap z horbit
  exact boundaryPairCurrent_invariant_of_covariance Γ (s.map ⟨Inv.inv, inv_injective⟩) s
    (fun g => μ g⁻¹) μ (reflected_jump_pos s μ hpos) hpos
    (reflected_support_generates s hgen) hgen νm νp
    (reflectedGeometricHittingMeasure_stationary Γ s μ hpos hmass hgen hgap z)
    (geometricHittingMeasure_stationary Γ s μ hpos hmass hgen hgap z) K hK g hc

end Singularity
