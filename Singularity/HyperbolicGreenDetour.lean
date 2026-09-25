import Singularity.GeometricDetour
import Singularity.KilledGreenDecay
import Singularity.KilledWalkTransport

/-!
# Superexponential decay of the Green function along detours

Finite support and an operator spectral gap imply a uniform bound
A exp(-c exp R) for the Green mass of paths avoiding the radius-R hyperbolic
ball, when their endpoint disk coordinates are separated by a fixed δ > 0.
This is a preliminary estimate for a geometric Martin-boundary argument,
not an Ancona inequality or a proof of boundary identification.
-/

noncomputable section
open Filter
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Exponential detour length and spectral decay bound the actual killed
Green series, with explicit dependence on the jump and spectral constants. -/
theorem killedGreen_hyperbolic_detour_bound (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q < 1)
    (hb : ∀ n : ℕ, ‖rightMarkov s μ ^ n‖ ≤ C * q ^ n)
    (R δ : ℝ) (x y : Γ)
    (hsep : δ ≤ dist (halfPlaneCayley (x • UpperHalfPlane.I))
      (halfPlaneCayley (y • UpperHalfPlane.I))) :
    killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) UpperHalfPlane.I < R} x y ≤
      C / (1 - q) * Real.exp (Real.log q *
        (δ / (4 * Real.exp (finiteJumpLengthBound Γ UpperHalfPlane.I s)) * Real.exp R)) := by
  apply killedGreen_le_real_cutoff s μ hμ hgap C q hC hq hq1 hb
  intro n hn
  exact killedWeight_eq_zero_of_short_detour Γ s μ R δ n x y hsep hn

/-- Uniform positive constants give double-exponential decay for separated
endpoints. No cocompactness, density comparison, or Martin kernel is assumed. -/
theorem killedGreen_hyperbolic_detour_decay (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (R : ℝ) (x y : Γ),
      δ ≤ dist (halfPlaneCayley (x • UpperHalfPlane.I))
        (halfPlaneCayley (y • UpperHalfPlane.I)) →
      killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) UpperHalfPlane.I < R} x y ≤
        A * Real.exp (-c * Real.exp R) := by
  obtain ⟨C, q, hC, hq, hq1, hb⟩ := markov_uniform_geometric_rate s μ hgap
  refine ⟨C / (1 - q), -Real.log q * (δ / (4 * Real.exp (finiteJumpLengthBound Γ UpperHalfPlane.I s))),
    div_pos hC (sub_pos.mpr hq1), mul_pos (neg_pos.mpr (Real.log_neg hq hq1)) (by positivity), ?_⟩
  intro R x y hsep
  simpa only [neg_mul, neg_neg, mul_assoc] using
    killedGreen_hyperbolic_detour_bound Γ s μ hμ hgap C q hC.le hq hq1 hb R δ x y hsep

/-- The hyperbolic ball and killed Green kernel translate together. -/
theorem killedGreen_hyperbolicBall_left (Γ : Subgroup SL(2, ℝ))
    (s : Finset Γ) (μ : Γ → ℝ) (R : ℝ) (u x y : Γ) :
    killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} x y =
      killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) UpperHalfPlane.I < R}
        (u⁻¹ * x) (u⁻¹ * y) := by
  have he : (fun g : Γ => u * g) ⁻¹'
      {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} =
      {g : Γ | dist (g • UpperHalfPlane.I) UpperHalfPlane.I < R} := by
    ext g
    change dist ((u * g) • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R ↔ _
    rw [mul_smul]
    change dist ((u : SL(2, ℝ)) • (g • UpperHalfPlane.I))
      ((u : SL(2, ℝ)) • UpperHalfPlane.I) < R ↔ _
    rw [dist_smul]
    rfl
  have h := killedGreen_left s μ
    {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R}
    u (u⁻¹ * x) (u⁻¹ * y)
  simpa only [mul_inv_cancel_left, he] using h

/-- The same detour constants work at every orbit center. Endpoint separation
is measured in the disk chart centered at that orbit point. -/
theorem killedGreen_hyperbolic_detour_decay_uniform_center (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (R : ℝ) (u x y : Γ),
      δ ≤ dist (halfPlaneCayley ((u⁻¹ * x) • UpperHalfPlane.I))
        (halfPlaneCayley ((u⁻¹ * y) • UpperHalfPlane.I)) →
      killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} x y ≤
        A * Real.exp (-c * Real.exp R) := by
  obtain ⟨A, c, hA, hc, hb⟩ := killedGreen_hyperbolic_detour_decay Γ s μ hμ hgap δ hδ
  refine ⟨A, c, hA, hc, ?_⟩
  intro R u x y hsep
  rw [killedGreen_hyperbolicBall_left]
  exact hb R (u⁻¹ * x) (u⁻¹ * y) hsep

/-- Bounded triangle excess replaces the disk-separation hypothesis by a
condition expressed entirely in hyperbolic distances. -/
theorem killedGreen_hyperbolic_detour_decay_of_excess (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D : ℝ) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (R : ℝ) (u x y : Γ),
      2 ≤ dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) →
      dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
        dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
        dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} x y ≤
        A * Real.exp (-c * Real.exp R) := by
  obtain ⟨A, c, hA, hc, hb⟩ := killedGreen_hyperbolic_detour_decay_uniform_center
    Γ s μ hμ hgap (Real.exp (-D / 2) / 4) (by positivity)
  refine ⟨A, c, hA, hc, ?_⟩
  intro R u x y hd hexcess
  exact hb R u x y (orbit_cayley_separation_of_excess Γ u x y D hd hexcess)

/-- Double-exponential decay eventually dominates every exponential rate,
including its fixed positive prefactor. -/
theorem double_exponential_eventually_le (A c K : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ R : ℝ in atTop, A * Real.exp (-c * Real.exp R) ≤ Real.exp (-K * R) := by
  have hh := ((Real.isLittleO_pow_exp_atTop (n := 0)).const_mul_left (Real.log A)).add
    ((Real.isLittleO_pow_exp_atTop (n := 1)).const_mul_left K)
  have hb := hh.bound hc
  filter_upwards [hb] with R hR
  simp only [pow_zero, mul_one, pow_one, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos R)] at hR
  have hl := (le_abs_self (Real.log A + K * R)).trans hR
  calc
    _ = Real.exp (Real.log A + -c * Real.exp R) := by rw [Real.exp_add, Real.exp_log hA]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- At any prescribed exponential rate, all sufficiently large avoided balls
have uniformly negligible Green mass between separated disk endpoints. -/
theorem killedGreen_hyperbolic_detour_superexponential (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (δ : ℝ) (hδ : 0 < δ) (K : ℝ) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ u x y : Γ,
      δ ≤ dist (halfPlaneCayley ((u⁻¹ * x) • UpperHalfPlane.I))
        (halfPlaneCayley ((u⁻¹ * y) • UpperHalfPlane.I)) →
      killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} x y ≤
        Real.exp (-K * R) := by
  obtain ⟨A, c, hA, hc, hb⟩ :=
    killedGreen_hyperbolic_detour_decay_uniform_center Γ s μ hμ hgap δ hδ
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (double_exponential_eventually_le A c K hA hc)
  exact ⟨R₀, fun R hR u x y hsep => (hb R u x y hsep).trans (hR₀ R hR)⟩

end Singularity
