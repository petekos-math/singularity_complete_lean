import Singularity.CocompactGreenBall
import Singularity.CocompactRelativeDetour

/-!
# A global Green product comparison with polynomial loss

Choose the avoided ball radius logarithmically in endpoint distance. The
absolute double-exponential detour bound is then at most half the full Green
kernel, using the independently proved coarse exponential lower bound.
The entrance comparison loses only a polynomial factor in endpoint distance.
This is weaker than an Ancona inequality with a distance-independent constant.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A logarithmic radius makes a double-exponential bound smaller than half
of a specified exponential lower bound, uniformly in nonnegative distance. -/
theorem exists_log_radius_absorption (a b A c : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hA : 0 < A) (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧ ∀ d ≥ 0,
      A * Real.exp (-c * Real.exp (Real.log (M * (1 + d)))) ≤
        (a / 2) * Real.exp (-b * d) := by
  let q := Real.log (2 * A / a)
  let M := (b + |q| + 1) / c
  have hM : 0 < M := div_pos (by positivity) hc
  have hcm : c * M = b + |q| + 1 := by dsimp [M]; field_simp
  have hq : q ≤ c * M := by rw [hcm]; linarith [le_abs_self q]
  have hbc : b ≤ c * M := by rw [hcm]; linarith [abs_nonneg q]
  have heA : (a / 2) * Real.exp q = A := by
    dsimp [q]
    rw [Real.exp_log (div_pos (mul_pos (by norm_num) hA) ha)]
    field_simp
  refine ⟨M, hM, ?_⟩
  intro d hd
  rw [Real.exp_log (mul_pos hM (by linarith))]
  have he : q + -c * (M * (1 + d)) ≤ -b * d := by
    have hm := mul_le_mul_of_nonneg_right hbc hd
    nlinarith
  calc
    _ = ((a / 2) * Real.exp q) * Real.exp (-c * (M * (1 + d))) := by rw [heA]
    _ = (a / 2) * Real.exp (q + -c * (M * (1 + d))) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)

/-- For bounded triangle excess at the intermediate orbit point, the Green
product comparison has a polynomial loss uniform over all endpoint distances.
The factor exp(p log(1+d)) is (1+d)^p. -/
theorem cocompact_walkGreen_polynomial_comparison (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D : ℝ) :
    ∃ H p : ℝ, 0 < H ∧ 0 ≤ p ∧ ∀ x u y : Γ,
      2 ≤ dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) →
      dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
        dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
        dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      walkGreen s μ x y ≤
        H * Real.exp (p * Real.log (1 + dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I))) *
        walkGreen s μ x u * walkGreen s μ u y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨a, b, ha, hb, hlower⟩ := cocompact_walkGreen_exp_lower Γ s μ hpos hgen hgap
  obtain ⟨A, c, hA, hc, hdetour⟩ := killedGreen_hyperbolic_detour_decay_of_excess Γ s μ hμ hgap D
  obtain ⟨C, p, hC, hp, hball⟩ := cocompact_walkGreen_ball_comparison Γ s μ hpos hmass hgen hgap
  obtain ⟨M, hM, habsorb⟩ := exists_log_radius_absorption a b A c ha hb.le hA hc
  refine ⟨2 * C * Real.exp (p * Real.log M), p, by positivity, hp, ?_⟩
  intro x u y hd hexcess
  let d := dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)
  let R := Real.log (M * (1 + d))
  have hd0 : 0 ≤ d := dist_nonneg
  have hkill : killedGreen s μ
      {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} x y ≤ walkGreen s μ x y / 2 := by
    apply (hdetour R u x y hd hexcess).trans
    apply (habsorb d hd0).trans
    have hh := div_le_div_of_nonneg_right (hlower x y) (show (0 : ℝ) ≤ 2 by norm_num)
    convert hh using 1
    ring
  have hbxy := hball R u x y
  have hprod : walkGreen s μ x y ≤
      2 * (C * Real.exp (p * R) * walkGreen s μ x u * walkGreen s μ u y) := by linarith
  have he : Real.exp (p * R) = Real.exp (p * Real.log M) * Real.exp (p * Real.log (1 + d)) := by
    dsimp [R]
    rw [Real.log_mul hM.ne' (by positivity), mul_add, Real.exp_add]
  rw [he] at hprod
  convert hprod using 1
  ring

/-- A global polynomial product bound, including short endpoint distances.
Only bounded triangle excess is required; no scale restriction remains. -/
theorem cocompact_walkGreen_polynomial_product_bound (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D : ℝ) :
    ∃ H p : ℝ, 0 < H ∧ 0 ≤ p ∧ ∀ x u y : Γ,
      dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
        dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
        dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      walkGreen s μ x y ≤
        H * (1 + dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)) ^ p *
        walkGreen s μ x u * walkGreen s μ u y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨H₀, p, hH₀, hp, hlarge⟩ :=
    cocompact_walkGreen_polynomial_comparison Γ s μ hpos hmass hgen hgap D
  obtain ⟨C, b, hC, _, hball⟩ := cocompact_walkGreen_ball_comparison Γ s μ hpos hmass hgen hgap
  let L := C * Real.exp (b * (D + 3))
  let H := max H₀ L
  have hH : 0 < H := hH₀.trans_le (le_max_left _ _)
  refine ⟨H, p, hH, hp, ?_⟩
  intro x u y hexcess
  let d := dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I)
  have hd : 0 ≤ d := dist_nonneg
  let E := Real.exp (p * Real.log (1 + d))
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hp (Real.log_nonneg (by linarith)))
  rw [Real.rpow_def_of_pos (show 0 < 1 + dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) by positivity)]
  rw [mul_comm (Real.log (1 + dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I))) p]
  change walkGreen s μ x y ≤ H * E * walkGreen s μ x u * walkGreen s μ u y
  have hmono {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂) :
      a₁ * walkGreen s μ x u * walkGreen s μ u y ≤ a₂ * walkGreen s μ x u * walkGreen s μ u y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (walkGreen_nonneg s μ hμ x u))
      (walkGreen_nonneg s μ hμ u y)
  by_cases hdist : 2 ≤ d
  · exact (hlarge x u y hdist hexcess).trans
      (hmono (mul_le_mul_of_nonneg_right (le_max_left H₀ L) (Real.exp_pos _).le))
  · have hx : x ∈ {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < D + 3} := by
      change dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) < D + 3
      have hn := dist_nonneg (x := y • UpperHalfPlane.I) (y := u • UpperHalfPlane.I)
      change dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
        dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) - d ≤ D at hexcess
      linarith
    have hs := hball (D + 3) u x y
    rw [killedGreen_of_mem s μ _ hx, zero_add] at hs
    apply hs.trans
    apply hmono
    exact (le_max_right H₀ L).trans (le_mul_of_one_le_right hH.le hE)

end Singularity
