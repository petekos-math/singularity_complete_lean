import Singularity.InteriorKilledGreen
import Singularity.RadialBarrier

/-!
# Interior estimates for the actual semicircular domains

The general excursion estimates apply to log-radius in any isometric chart.
Consequently killed Green kernels have uniform positive local lower bounds
and local Harnack comparison at a fixed depth inside these domains.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hgen hgap in
/-- Uniform positive local lower bounds for every radial half-plane domain. -/
theorem radial_killedGreen_uniform_lower (D : ℝ) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧ ∀ (q : SL(2, ℝ)) (r : ℝ) (x y : Γ),
      dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      r + R ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)) →
      r + R ≤ axisRadialCoordinate (q • (y • UpperHalfPlane.I)) →
      ε ≤ killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y := by
  let L := finiteJumpLengthBound Γ UpperHalfPlane.I s + 1
  have hL : 0 < L := by dsimp [L]; linarith [finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s]
  obtain ⟨R,ε,hR,hε,hlower⟩ := interior_killedGreen_uniform_lower Γ s μ hpos hgen hgap L D hL
  refine ⟨R,ε,hR,hε,?_⟩
  intro q r x y hxy hx hy
  exact hlower (fun g => axisRadialCoordinate (q • (g • UpperHalfPlane.I))) r
    (fun x g hg => (axisRadialCoordinate_jump_bound Γ s q UpperHalfPlane.I x g hg).trans
      (by dsimp [L]; linarith))
    (radialOrbitSublevel Γ q UpperHalfPlane.I r) (fun _ ha => ha) x y hxy hx hy

variable [Countable Γ]

include hpos hgen hgap in
/-- Uniform local Harnack comparison in radial domains, valid for all targets. -/
theorem radial_killedGreen_uniform_harnack (hmass : ∑ g ∈ s, μ g = 1) (D : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 1 ≤ C ∧ ∀ (q : SL(2, ℝ)) (r : ℝ) (x o : Γ),
      dist (x • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ D →
      r + R ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)) →
      r + R ≤ axisRadialCoordinate (q • (o • UpperHalfPlane.I)) → ∀ y : Γ,
      killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) o y ≤
        C * killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y := by
  let L := finiteJumpLengthBound Γ UpperHalfPlane.I s + 1
  have hL : 0 < L := by dsimp [L]; linarith [finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s]
  obtain ⟨R,C,hR,hC,hlocal⟩ := interior_killedGreen_uniform_harnack Γ s μ hpos hmass hgen hgap L D hL
  refine ⟨R,C,hR,hC,?_⟩
  intro q r x o hxo hx ho y
  exact hlocal (fun g => axisRadialCoordinate (q • (g • UpperHalfPlane.I))) r
    (fun x g hg => (axisRadialCoordinate_jump_bound Γ s q UpperHalfPlane.I x g hg).trans
      (by dsimp [L]; linarith))
    (radialOrbitSublevel Γ q UpperHalfPlane.I r) (fun _ ha => ha) x o hxo hx ho y

end Singularity
