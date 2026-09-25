import Singularity.SupportedCoordinates
import Singularity.CyclicOrbits
import Singularity.GreenBoundary
import Singularity.ExponentialLattice
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Green boundary limits in finite cyclic-orbit coordinates

The compressed inverse is transported by an actual linear isometric equivalence.
Finite families of exponential orbit bounds supply the required summability.
The normalized geometric separator is constructed in GeometricStrip.lean.
GreenPoissonBounds.lean derives its envelopes from the distance comparison
and bounded-distance ray approaches. The geometric boundary limits remain open.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Singularity

variable {J : Type*}

/-- Exponential square envelopes are summable on any finite collection of integer orbits. -/
theorem summable_orbit_exp_sq [Fintype J] {τ : ℝ} (hτ : 0 < τ) (C : J → ℝ) :
    Summable (fun p : ℤ × J => (C p.2 * Real.exp (-τ * |(p.1 : ℝ)|)) ^ 2) := by
  apply (summable_prod_of_nonneg (fun p => sq_nonneg _)).mpr
  constructor
  · intro n
    exact (hasSum_fintype _).summable
  · simp only [tsum_fintype]
    exact summable_sum (fun j _ => summable_exp_abs_int_sq hτ (C j))

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- Cyclic coordinates give the concrete Hilbert-space equivalence needed by Fourier analysis. -/
def cyclicSupportedCoordinates (a : Γ) (b : J → Γ) (ha : ¬IsOfFinOrder a)
    (hb : ∀ j k (n : ℤ), a ^ n * b j = b k → j = k) :
    supportedL2 (cyclicOrbitUnion a b) ≃ₗᵢ[ℂ] SequenceL2 (ℤ × J) :=
  supportedCoordinatesEquiv (cyclicOrbitEquiv a b ha hb)

omit [MeasurableMul Γ] in
theorem cyclicSupportedCoordinates_apply (a : Γ) (b : J → Γ) (ha : ¬IsOfFinOrder a)
    (hb : ∀ j k (n : ℤ), a ^ n * b j = b k → j = k)
    (f : supportedL2 (cyclicOrbitUnion a b)) (n : ℤ) (j : J) :
    cyclicSupportedCoordinates a b ha hb f (n, j) = (f : GroupL2 Γ) (a ^ n * b j) := rfl

variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  {A : Set Γ} (e : (ℤ × J) ≃ A)

/-- The actual compressed Green inverse in the orbit sequence space. -/
def orbitGreenInverse : SequenceL2 (ℤ × J) →L[ℂ] SequenceL2 (ℤ × J) :=
  coordinateOperator e (walkGreenCompression s μ hμ hmass hgap A).symm.toContinuousLinearMap

/-- Coordinate transport retains the coercivity-derived inverse bound. -/
theorem orbitGreenInverse_norm : ‖orbitGreenInverse s μ hμ hmass hgap e‖ ≤ 2 := by
  rw [orbitGreenInverse, coordinateOperator_norm]
  exact walkGreenCompression_inverse_norm s μ hμ hmass hgap A

/-- Normalized row in the same coordinates as the analysis operator. -/
def orbitGreenRow (x : Γ) (r : ℝ) : SequenceL2 (ℤ × J) :=
  supportedCoordinatesEquiv e (normalizedGreenRow s μ A x r)

/-- Normalized column in the same coordinates as the analysis operator. -/
def orbitGreenColumn (y : Γ) (c : ℝ) : SequenceL2 (ℤ × J) :=
  supportedCoordinatesEquiv e (normalizedGreenColumn s μ A y c)

include hgap in
theorem orbitGreenRow_apply (x : Γ) (r : ℝ) (p : ℤ × J) :
    orbitGreenRow s μ e x r p = (walkGreen s μ x (e p) : ℂ) / (r : ℂ) :=
  normalizedGreenRow_apply s μ hgap A x r (e p)

include hgap in
theorem orbitGreenColumn_apply (y : Γ) (c : ℝ) (p : ℤ × J) :
    orbitGreenColumn s μ e y c p = (walkGreen s μ (e p) y : ℂ) / (c : ℂ) :=
  normalizedGreenColumn_apply s μ hgap A y c (e p)

/-- The actual separator pairing in the ℤ × J sequence Hilbert space. -/
theorem orbitGreen_separator_pairing (x y : Γ) (r c : ℝ)
    (hsep : SeparatesJumpPaths s A x y) :
    (walkGreen s μ x y : ℂ) / ((r : ℂ) * (c : ℂ)) = inner ℂ
      (orbitGreenRow s μ e x r)
      (orbitGreenInverse s μ hμ hmass hgap e (orbitGreenColumn s μ e y c)) := by
  unfold orbitGreenRow orbitGreenColumn orbitGreenInverse
  rw [coordinateOperator_pairing]
  exact normalizedGreen_separator_pairing s μ hμ hmass hgap A x y r c hsep

/-- Exponential bounds on finitely many orbits justify the normalized Green limit.
The hypotheses refer directly to scalar path Green quotients on those orbits. -/
theorem orbitGreen_boundary_limit [Fintype J] {α : Type*} {l : Filter α} [l.NeBot]
    (x y : α → Γ) (r c : α → ℝ) (u₀ v₀ : (ℤ × J) → ℂ)
    {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (C D : J → ℝ)
    (hsep : ∀ᶠ n in l, SeparatesJumpPaths s A (x n) (y n))
    (hu : ∀ᶠ n in l, ∀ p : ℤ × J,
      ‖(walkGreen s μ (x n) (e p) : ℂ) / (r n : ℂ)‖ ≤
        C p.2 * Real.exp (-τ * |(p.1 : ℝ)|))
    (hv : ∀ᶠ n in l, ∀ p : ℤ × J,
      ‖(walkGreen s μ (e p) (y n) : ℂ) / (c n : ℂ)‖ ≤
        D p.2 * Real.exp (-σ * |(p.1 : ℝ)|))
    (hup : ∀ p, Tendsto (fun n => (walkGreen s μ (x n) (e p) : ℂ) / (r n : ℂ)) l (𝓝 (u₀ p)))
    (hvp : ∀ p, Tendsto (fun n => (walkGreen s μ (e p) (y n) : ℂ) / (c n : ℂ)) l (𝓝 (v₀ p))) :
    ∃ u v : SequenceL2 (ℤ × J),
      (∀ p, u p = u₀ p) ∧ (∀ p, v p = v₀ p) ∧
      Tendsto (fun n => orbitGreenRow s μ e (x n) (r n)) l (𝓝 u) ∧
      Tendsto (fun n => orbitGreenColumn s μ e (y n) (c n)) l (𝓝 v) ∧
      Tendsto (fun n => (walkGreen s μ (x n) (y n) : ℂ) / ((r n : ℂ) * (c n : ℂ)))
        l (𝓝 (inner ℂ u (orbitGreenInverse s μ hμ hmass hgap e v))) := by
  have hu' : ∀ᶠ n in l, ∀ p, ‖orbitGreenRow s μ e (x n) (r n) p‖ ≤
      C p.2 * Real.exp (-τ * |(p.1 : ℝ)|) := by
    simpa only [orbitGreenRow_apply s μ hgap] using hu
  have hv' : ∀ᶠ n in l, ∀ p, ‖orbitGreenColumn s μ e (y n) (c n) p‖ ≤
      D p.2 * Real.exp (-σ * |(p.1 : ℝ)|) := by
    simpa only [orbitGreenColumn_apply s μ hgap] using hv
  have hup' : ∀ p, Tendsto (fun n => orbitGreenRow s μ e (x n) (r n) p) l (𝓝 (u₀ p)) := by
    simpa only [orbitGreenRow_apply s μ hgap] using hup
  have hvp' : ∀ p, Tendsto (fun n => orbitGreenColumn s μ e (y n) (c n) p) l (𝓝 (v₀ p)) := by
    simpa only [orbitGreenColumn_apply s μ hgap] using hvp
  obtain ⟨u, hueq, hut⟩ := sequenceL2_limit_exists (summable_orbit_exp_sq hτ C) hu' hup'
  obtain ⟨v, hveq, hvt⟩ := sequenceL2_limit_exists (summable_orbit_exp_sq hσ D) hv' hvp'
  refine ⟨u, v, hueq, hveq, hut, hvt, ?_⟩
  apply (pairing_tendsto (orbitGreenInverse s μ hμ hmass hgap e) hut hvt).congr'
  filter_upwards [hsep] with n hn
  exact (orbitGreen_separator_pairing s μ hμ hmass hgap e (x n) (y n) (r n) (c n) hn).symm

end Singularity
