import Singularity.CocompactRadialLower
import Singularity.HyperbolicGreenDetour

/-!
# Relative detour bounds inside radial domains

The absolute hyperbolic detour bound also bounds paths killed on a second set.
Dividing by the actual coarse killed Green lower bound yields arbitrarily fast
exponential relative error for endpoints in a fixed deep axis tube and segment
length at most a fixed multiple of the detour radius.
-/

noncomputable section
open Filter
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- A detour estimate normalized by the killed Green function itself. The tube
and depth conditions are explicit, as is the linear endpoint-length restriction. -/
theorem cocompact_radial_relative_green_detour
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (E D B K : ℝ) :
    ∃ H R₀ : ℝ, 0 < H ∧ ∀ R ≥ R₀, ∀ (q : SL(2, ℝ)) (r a b : ℝ) (u x y : Γ),
      a ≤ b → r+H ≤ a →
      dist (q • (x • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I a) ≤ E →
      dist (q • (y • UpperHalfPlane.I)) (verticalHeightRay UpperHalfPlane.I b) ≤ E →
      b-a ≤ B*R → 2 ≤ dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) →
      dist (x • UpperHalfPlane.I) (u • UpperHalfPlane.I) +
        dist (y • UpperHalfPlane.I) (u • UpperHalfPlane.I) -
        dist (x • UpperHalfPlane.I) (y • UpperHalfPlane.I) ≤ D →
      killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r ∪
        {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R}) x y ≤
        Real.exp (-K*R) * killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨H,α,β,hH,hα,hβ,hlower⟩ := cocompact_radial_killedGreen_exp_lower Γ s μ hpos hmass hgen hgap E
  obtain ⟨A,c,hA,hc,hdetour⟩ := killedGreen_hyperbolic_detour_decay_of_excess Γ s μ hμ hgap D
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp
    (double_exponential_eventually_le (A/α) c (K+β*B) (div_pos hA hα) hc)
  refine ⟨H,R₀,hH,?_⟩
  intro R hR q r a b u x y hab hdepth hx hy hlen hdist hexcess
  have hl : α * Real.exp (-β*(B*R)) ≤
      killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I r) x y := by
    apply le_trans _ (hlower q r a b x y hab hdepth hx hy)
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlen (neg_nonpos.mpr hβ.le))) hα.le
  calc
    _ ≤ killedGreen s μ {g : Γ | dist (g • UpperHalfPlane.I) (u • UpperHalfPlane.I) < R} x y :=
      killedGreen_antitone s μ hμ hmass hgap _ _ (Set.subset_union_right) x y
    _ ≤ A * Real.exp (-c*Real.exp R) := hdetour R u x y hdist hexcess
    _ = α * ((A/α) * Real.exp (-c*Real.exp R)) := by field_simp
    _ ≤ α * Real.exp (-(K+β*B)*R) := mul_le_mul_of_nonneg_left (hR₀ R hR) hα.le
    _ = Real.exp (-K*R) * (α * Real.exp (-β*(B*R))) := by
      rw [mul_left_comm (Real.exp (-K*R)) α, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le

end Singularity
