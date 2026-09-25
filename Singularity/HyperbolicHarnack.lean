import Singularity.GreenHarnack
import Singularity.HyperbolicOrbitGrowth

/-!
# Uniform local Harnack comparison in a discrete hyperbolic orbit

Only finitely many group vertices move i a bounded distance. The individual
path Harnack constants therefore give one comparison constant for all pairs
of starting vertices at bounded hyperbolic distance, uniformly in the target.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A fixed hyperbolic displacement bound gives a uniform Green-row Harnack
constant, including possible stabilizer multiplicities. -/
theorem hyperbolic_uniform_greenHarnack (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (R : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x z y : Γ,
      dist (x • UpperHalfPlane.I) (z • UpperHalfPlane.I) ≤ R →
      walkGreen s μ z y ≤ C * walkGreen s μ x y := by
  choose c hc hb using fun g : Γ => exists_greenHarnackConstant s μ hgap hpos hgen 1 g
  let C := 1 + ∑ g ∈ hyperbolicOrbitBall Γ R, c g
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (fun g (_ : g ∈ hyperbolicOrbitBall Γ R) => (hc g).le)]
  refine ⟨C, hC, ?_⟩
  intro x z y hxz
  have hdist : dist ((x⁻¹ * z) • UpperHalfPlane.I) UpperHalfPlane.I =
      dist (z • UpperHalfPlane.I) (x • UpperHalfPlane.I) := by
    rw [← dist_smul (x : SL(2, ℝ))]
    change dist (x • ((x⁻¹ * z) • UpperHalfPlane.I)) (x • UpperHalfPlane.I) = _
    rw [← mul_smul, mul_inv_cancel_left]
  have hm : x⁻¹ * z ∈ hyperbolicOrbitBall Γ R := by
    rw [mem_hyperbolicOrbitBall, hdist, dist_comm]
    exact hxz
  have hcC : c (x⁻¹ * z) ≤ C := by
    have hh := Finset.single_le_sum (fun g (_ : g ∈ hyperbolicOrbitBall Γ R) => (hc g).le) hm
    dsimp [C]
    linarith
  have h := (hb (x⁻¹ * z) (x⁻¹ * y)).trans
    (mul_le_mul_of_nonneg_right hcC (walkGreen_nonneg s μ (fun g hg => (hpos g hg).le) _ _))
  have hleft := walkGreen_left s μ x (x⁻¹ * z) (x⁻¹ * y)
  have hone := walkGreen_left s μ x 1 (x⁻¹ * y)
  simp only [mul_inv_cancel_left, mul_one] at hleft hone
  rwa [← hleft, ← hone] at h

/-- Iterating a local comparison along any finite orbit chain. -/
theorem greenHarnack_along_chain (Γ : Subgroup SL(2, ℝ))
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (C R : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x z y : Γ, dist (x • UpperHalfPlane.I) (z • UpperHalfPlane.I) ≤ R →
      walkGreen s μ z y ≤ C * walkGreen s μ x y)
    (f : ℕ → Γ) (n : ℕ)
    (hf : ∀ k < n, dist (f k • UpperHalfPlane.I) (f (k + 1) • UpperHalfPlane.I) ≤ R)
    (y : Γ) : walkGreen s μ (f n) y ≤ C ^ n * walkGreen s μ (f 0) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ C * walkGreen s μ (f n) y := hb _ _ _ (hf n (Nat.lt_succ_self n))
      _ ≤ C * (C ^ n * walkGreen s μ (f 0) y) :=
        mul_le_mul_of_nonneg_left (ih (fun k hk => hf k (Nat.lt_trans hk (Nat.lt_succ_self n)))) hC
      _ = _ := by rw [pow_succ]; ring

end Singularity
