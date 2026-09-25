import Singularity.CompactBoundary

/-!
# The closed ideal arc of a chart half-plane

The negative half-plane in a special-linear chart can accumulate only on
its closed nonpositive ideal arc, which includes the two chart endpoints.
This supplies the boundary-closure condition for geometric trapping regions.
-/

noncomputable section
open Set OnePoint Filter
open scoped Classical MatrixGroups UpperHalfPlane Topology
namespace Singularity

/-- The closed ideal arc on the nonpositive side of a special-linear chart. -/
def chartNonpositiveBoundaryArc (B : SL(2, ℝ)) : Set (OnePoint ℝ) :=
  (fun ξ : OnePoint ℝ => B⁻¹ • ξ) ⁻¹' (((↑) : ℝ → OnePoint ℝ) '' Ioi 0)ᶜ

/-- The ideal arc includes its endpoints and is closed. -/
theorem isClosed_chartNonpositiveBoundaryArc (B : SL(2, ℝ)) :
    IsClosed (chartNonpositiveBoundaryArc B) :=
  (OnePoint.isOpen_image_coe.mpr isOpen_Ioi).isClosed_compl.preimage (continuous_const_smul B⁻¹)

/-- Orbit points on the negative side can have no positive finite ideal
limit in the same chart. -/
theorem boundary_mem_arc_of_negative_chart_closure
    {Γ : Type*} [SMul Γ ℍ] (z : ℍ) (B : SL(2, ℝ)) (ξ : OnePoint ℝ)
    (hξ : compactBoundaryEmbedding ξ ∈ closure
      ((fun v : Γ => hyperbolicCompactEmbedding (v • z)) ''
        {v : Γ | (B⁻¹ • (v • z)).re < 0})) :
    ξ ∈ chartNonpositiveBoundaryArc B := by
  let O : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' {w : ℂ | 0 < w.re}
  have hO : IsOpen O := OnePoint.isOpen_image_coe.mpr (isOpen_lt continuous_const Complex.continuous_re)
  have hclosed : IsClosed ((fun w : OnePoint ℂ => B⁻¹ • w) ⁻¹' Oᶜ) :=
    hO.isClosed_compl.preimage (continuous_const_smul B⁻¹)
  have hsub : ((fun v : Γ => hyperbolicCompactEmbedding (v • z)) ''
      {v : Γ | (B⁻¹ • (v • z)).re < 0}) ⊆ (fun w : OnePoint ℂ => B⁻¹ • w) ⁻¹' Oᶜ := by
    rintro _ ⟨v, hv, rfl⟩
    change B⁻¹ • hyperbolicCompactEmbedding (v • z) ∉ O
    rw [← hyperbolicCompactEmbedding_smul]
    rintro ⟨w, hw, he⟩
    have he' : w = ((B⁻¹ • (v • z) : ℍ) : ℂ) := OnePoint.coe_injective he
    subst w
    change 0 < (B⁻¹ • (v • z)).re at hw
    exact (not_lt_of_ge hw.le) hv
  have hnot := closure_minimal hsub hclosed hξ
  change B⁻¹ • ξ ∉ ((↑) : ℝ → OnePoint ℝ) '' Ioi 0
  rintro ⟨t, ht, he⟩
  apply hnot
  change B⁻¹ • compactBoundaryEmbedding ξ ∈ O
  rw [← compactBoundaryEmbedding_smul, ← he]
  exact ⟨(t : ℂ), ht, rfl⟩

/-- Convergence to an interior point of the negative ideal arc eventually
places the hyperbolic sequence on the negative side of the chart. -/
theorem eventually_negative_chart_of_boundary_tendsto
    {ι : Type*} {l : Filter ι} (w : ι → ℍ) (B : SL(2, ℝ)) (ξ : OnePoint ℝ)
    (ht : Tendsto (fun n => hyperbolicCompactEmbedding (w n)) l
      (𝓝 (compactBoundaryEmbedding ξ)))
    (hξ : ∃ r : ℝ, r < 0 ∧ B⁻¹ • ξ = (r : OnePoint ℝ)) :
    ∀ᶠ n in l, (B⁻¹ • w n).re < 0 := by
  obtain ⟨r, hr, hξ⟩ := hξ
  let O : Set (OnePoint ℂ) := ((↑) : ℂ → OnePoint ℂ) '' {v : ℂ | v.re < 0}
  have hO : IsOpen O := OnePoint.isOpen_image_coe.mpr
    (isOpen_lt Complex.continuous_re continuous_const)
  have hlim := (continuous_const_smul B⁻¹ :
    Continuous (fun v : OnePoint ℂ => B⁻¹ • v)).tendsto
      (compactBoundaryEmbedding ξ) |>.comp ht
  have hmem : B⁻¹ • compactBoundaryEmbedding ξ ∈ O := by
    rw [← compactBoundaryEmbedding_smul, hξ]
    exact ⟨(r : ℂ), hr, rfl⟩
  filter_upwards [hlim.eventually (hO.mem_nhds hmem)] with n hn
  change B⁻¹ • hyperbolicCompactEmbedding (w n) ∈ O at hn
  rw [← hyperbolicCompactEmbedding_smul] at hn
  obtain ⟨v, hv, he⟩ := hn
  have he' : v = ((B⁻¹ • w n : ℍ) : ℂ) := OnePoint.coe_injective he
  have hv' : v.re < 0 := hv
  rw [he'] at hv'
  exact hv'

end Singularity
