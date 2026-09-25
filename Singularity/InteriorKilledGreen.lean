import Singularity.CoordinateGreenLoss
import Singularity.HyperbolicHarnack

/-!
# Uniform local Green lower bounds inside a surviving domain

Discreteness and semigroup generation give a positive unrestricted Green lower
bound for nearby vertices. Deep enough above a killing sublevel, the proved
spectral loss is less than half this bound. This gives actual positive killed
Green values, uniformly in the coordinate, its level, and the killing set.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- A positive connection inside the surviving domain compares its Green rows
for every target, including targets close to the killing boundary. -/
theorem killedGreen_row_le_of_connection_lower
    {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (x o y : Γ) (ε : ℝ) (hε : 0 < ε)
    (hlower : ε ≤ killedGreen s μ A x o) :
    killedGreen s μ A o y ≤ (walkGreen s μ 1 1 / ε) * killedGreen s μ A x y := by
  have hdiag : killedGreen s μ A o o ≤ walkGreen s μ 1 1 := by
    have he := walkGreen_left s μ o 1 1
    simp only [mul_one] at he
    exact (killedGreen_le_green s μ hμ hgap A o o).trans_eq he
  have hh : ε * killedGreen s μ A o y ≤ walkGreen s μ 1 1 * killedGreen s μ A x y := by
    calc
      _ ≤ killedGreen s μ A x o * killedGreen s μ A o y :=
        mul_le_mul_of_nonneg_right hlower (killedGreen_nonneg s μ hμ A o y)
      _ ≤ killedGreen s μ A o o * killedGreen s μ A x y :=
        killedGreen_product_le s μ hμ hmass hgap A x o y
      _ ≤ _ := mul_le_mul_of_nonneg_right hdiag (killedGreen_nonneg s μ hμ A x y)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hε).mpr
  simpa only [mul_comm] using hh

/-- Nearby vertices sufficiently deep above any bounded-jump killing sublevel
have a uniform positive killed Green lower bound. No cocompactness is needed. -/
theorem interior_killedGreen_uniform_lower
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (L D : ℝ) (hL : 0 < L) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧ ∀ (h : Γ → ℝ) (r : ℝ),
      (∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L) →
      ∀ A : Set Γ, (∀ a ∈ A, h a ≤ r) → ∀ x y : Γ,
      dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      r + R ≤ h x → r + R ≤ h y → ε ≤ killedGreen s μ A x y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨H,hH,hlocal⟩ := hyperbolic_uniform_greenHarnack Γ s μ hpos hgen hgap D
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  obtain ⟨C,c,hC,hc,hloss⟩ := coordinate_green_killing_loss_decay s μ hμ hgap L hL
  let R := (|Real.log (2*C*H)|+1)/(2*c)
  have hR : 0 < R := div_pos (by positivity) (by positivity)
  have hReq : 2*c*R = |Real.log (2*C*H)|+1 := by
    dsimp [R]
    field_simp
  refine ⟨R, 1/(2*H), hR, by positivity, ?_⟩
  intro h r hjump A hA x y hxy hx hy
  have hg : 1/H ≤ walkGreen s μ x y := by
    apply (div_le_iff₀ hHp).mpr
    have hh := (walkGreen_diag_ge_one s μ hμ hgap y).trans (hlocal x y y hxy)
    simpa only [mul_comm] using hh
  have he : walkGreen s μ x y - killedGreen s μ A x y ≤ 1/(2*H) := by
    apply (hloss h r hjump A hA x y).trans
    calc
      C * Real.exp (-c * (h x+h y-2*r)) ≤ C * Real.exp (-Real.log (2*C*H)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
        have hh := le_abs_self (Real.log (2*C*H))
        have hd : 2*R ≤ h x+h y-2*r := by linarith
        have hm := mul_le_mul_of_nonneg_left hd hc.le
        nlinarith
      _ = 1/(2*H) := by
        rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2*C*H)]
        field_simp
  have hh : (1:ℝ)/H = 1/(2*H)+1/(2*H) := by ring
  linarith

/-- Local Harnack comparison for the actual killed walk, with uniform constants
in every coordinate domain at a sufficient distance from its killing boundary. -/
theorem interior_killedGreen_uniform_harnack
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (L D : ℝ) (hL : 0 < L) :
    ∃ R C : ℝ, 0 < R ∧ 1 ≤ C ∧ ∀ (h : Γ → ℝ) (r : ℝ),
      (∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L) →
      ∀ A : Set Γ, (∀ a ∈ A, h a ≤ r) → ∀ x o : Γ,
      dist (x • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ D →
      r + R ≤ h x → r + R ≤ h o → ∀ y : Γ,
      killedGreen s μ A o y ≤ C * killedGreen s μ A x y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨R,ε,hR,hε,hlower⟩ := interior_killedGreen_uniform_lower Γ s μ hpos hgen hgap L D hL
  let C := walkGreen s μ 1 1 / ε + 1
  have hC : 1 ≤ C := by
    have hh := div_nonneg (walkGreen_nonneg s μ hμ 1 1) hε.le
    dsimp [C]
    linarith
  refine ⟨R,C,hR,hC,?_⟩
  intro h r hjump A hA x o hxo hx ho y
  have hh := killedGreen_row_le_of_connection_lower s μ hμ hmass hgap A x o y ε hε
    (hlower h r hjump A hA x o hxo hx ho)
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (killedGreen_nonneg s μ hμ A x y)

end Singularity
