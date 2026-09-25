import Singularity.WalkBoundaryLaw

/-!
# Boundary equivariance at every deterministic time

Iteration of the almost-sure first-step relation identifies the boundary
point with the current group position acting on the independent future limit.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical
namespace Singularity

/-- The first-step relation iterates to any finite prefix. -/
theorem walkBoundaryMap_time_cocycle
    {Γ B : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    [MulAction Γ B] (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (b : (ℕ → s) → B)
    (hstep : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      b ω = (ω 0 : Γ) • b (fun k => ω (k + 1))) (n : ℕ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      b ω = walkPosition s 1 n ω • b (fun k => ω (k + n)) := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun ω => by simp [walkPosition_zero])
  | succ n ih =>
    have hshift : MeasurePreserving (fun (ω : ℕ → s) k => ω (k + 1))
        (infiniteWalkLaw s μ hμ hmass) (infiniteWalkLaw s μ hμ hmass) :=
      ⟨by fun_prop, infiniteWalkLaw_shift s μ hμ hmass 1⟩
    filter_upwards [hstep, hshift.quasiMeasurePreserving.ae ih] with ω hω hn
    rw [hω, hn, walkPosition_first_step, mul_smul]
    rfl

end Singularity
