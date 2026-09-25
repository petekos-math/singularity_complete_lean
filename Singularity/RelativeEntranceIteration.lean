import Singularity.RelativePairTransfer
import Singularity.LocalTransferIteration
import Singularity.RadialKilledGreen
import Singularity.KilledGreenChains

/-!
# Finite entrance iteration for an actual killed Green kernel

The first/last-entrance iteration now retains one fixed original killing set.
It gives a uniform product estimate when the relative detour errors are small
and all successor pairs remain admissible. The terminal comparison is proved
for nearby deep vertices in radial domains, using their actual killed Harnack
bound. Construction of the full geometric sequence remains separate.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Actual relative transfers give the factor-two product bound whenever their
local relative errors sum to at most one half. -/
theorem relative_finite_entrance_iteration_bound {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (N : ℕ) (B : ℕ → Finset Γ) (last : ℕ → Bool)
    (S : ℕ → Set (Γ × Γ)) (ε : ℕ → ℝ) (o : Γ) (C : ℝ) (hC : 0 ≤ C)
    (hε : ∀ n < N, 0 ≤ ε n) (hsum : ∑ n ∈ Finset.range N, ε n ≤ 1/2)
    (hmove : ∀ n < N, ∀ p ∈ S n, ∀ b : B n,
      (if last n then (p.1, (b : Γ)) else ((b : Γ), p.2)) ∈ S (n+1))
    (herror : ∀ n < N, ∀ p ∈ S n,
      killedGreen s μ (A ∪ (B n : Set Γ)) p.1 p.2 ≤ ε n * killedGreen s μ A p.1 p.2)
    (hterminal : ∀ p ∈ S N,
      killedGreen s μ A p.1 p.2 ≤ C * (killedGreen s μ A p.1 o * killedGreen s μ A o p.2)) :
    ∀ p ∈ S 0, killedGreen s μ A p.1 p.2 ≤
      2*C * (killedGreen s μ A p.1 o * killedGreen s μ A o p.2) := by
  apply local_transfer_half_error_bound N (fun n => relativePairTransfer s μ A (B n) (last n))
    S ε (fun p => killedGreen s μ A p.1 p.2)
    (fun p => killedGreen s μ A p.1 o * killedGreen s μ A o p.2) C hC
    (fun p => killedGreen_nonneg s μ hμ A p.1 p.2) hε hsum
  · intro n hn f g hh
    exact relativePairTransfer_monoOn s μ hμ A (B n) (last n) (S n) (S (n+1))
      (hmove n hn) f g hh
  · intro n _ p _
    exact relativePairTransfer_product_le s μ hμ hmass hgap A (B n) (last n) o p
  · intro n hn p hp
    have he := relativePairTransfer_green_decomposition s μ hμ hmass hgap A (B n) (last n) p
    have hh := herror n hn p hp
    linarith
  · exact hterminal

/-- The terminal relative product estimate is automatic when the first endpoint
and the intermediate vertex are nearby and both deep inside the radial domain. -/
theorem radial_near_center_killedGreen_product_bound
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (D : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ (q : SL(2, ℝ)) (r : ℝ) (x o y : Γ),
      dist (x • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ D →
      r+R ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)) →
      r+R ≤ axisRadialCoordinate (q • (o • UpperHalfPlane.I)) →
      killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y ≤
        C * (killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x o *
          killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) o y) := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨R,c,hR,hc,hlocal⟩ := radial_killedGreen_uniform_harnack Γ s μ hpos hgen hgap hmass D
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  refine ⟨R,c^2,hR,sq_pos_of_pos hcp,?_⟩
  intro q r x o y hxo hx ho
  let A := radialOrbitSublevel Γ q UpperHalfPlane.I r
  have hoA : o ∉ A := by
    intro hh
    change axisRadialCoordinate (q • (o • UpperHalfPlane.I)) ≤ r at hh
    linarith
  have hleft := hlocal q r o x (by simpa only [dist_comm] using hxo) ho hx y
  have hright := (killedGreen_diag_ge_one s μ hμ hgap A o hoA).trans
    (hlocal q r x o hxo hx ho o)
  calc
    _ ≤ c * killedGreen s μ A o y := hleft
    _ ≤ (c * killedGreen s μ A x o) * (c * killedGreen s μ A o y) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hright
        (mul_nonneg hcp.le (killedGreen_nonneg s μ hμ A o y))
    _ = _ := by ring

end Singularity
