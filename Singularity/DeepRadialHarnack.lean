import Singularity.DeepRadialGreenLower

/-!
# Exponential Harnack comparison throughout a deep radial domain

The coarse lower bound on killed connections gives row comparison with cost
exponential in the distance between the starting vertices. The depth buffer is
fixed, independent of this distance and of the target.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Global row comparison for the killed kernel within the fixed deep region. -/
theorem cocompact_deep_radial_greenHarnack
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ H C β : ℝ, 0 < H ∧ 1 ≤ C ∧ 0 < β ∧ ∀ (q : SL(2, ℝ)) (r : ℝ) (x z y : Γ),
      r+H ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)) →
      r+H ≤ axisRadialCoordinate (q • (z • UpperHalfPlane.I)) →
      killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) z y ≤
        (C * Real.exp (β*dist (x • UpperHalfPlane.I) (z • UpperHalfPlane.I))) *
          killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨H,α,β,hH,hα,hβ,hlower⟩ := cocompact_deep_radial_killedGreen_exp_lower Γ s μ hpos hmass hgen hgap
  let C := walkGreen s μ 1 1/α+1
  have hC : 1 ≤ C := by
    have hh := div_nonneg (walkGreen_nonneg s μ hμ 1 1) hα.le
    dsimp [C]; linarith
  refine ⟨H,C,β,hH,hC,hβ,?_⟩
  intro q r x z y hx hz
  let d := dist (x • UpperHalfPlane.I) (z • UpperHalfPlane.I)
  have hh := killedGreen_row_le_of_connection_lower s μ hμ hmass hgap
    (radialOrbitSublevel Γ q UpperHalfPlane.I r) x z y (α*Real.exp (-β*d))
    (mul_pos hα (Real.exp_pos _)) (hlower q r x z hx hz)
  have he : walkGreen s μ 1 1/(α*Real.exp (-β*d)) =
      (walkGreen s μ 1 1/α)*Real.exp (β*d) := by
    rw [neg_mul, Real.exp_neg]
    field_simp
  rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (killedGreen_nonneg s μ hμ _ x y)
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.exp_pos _).le

end Singularity
