import Singularity.GeometricMartinContinuity
import Singularity.MartinAction
import Singularity.PoissonMobius

/-!
# Covariance of the constructed geometric Martin map

The finite real-chart map intertwines the actual Martin-boundary action with
the Möbius action wherever the transformed endpoint is finite. The kernel
formula follows from the exact action on finite Green quotients and the now
proved convergence along arbitrary approaches.
-/

noncomputable section
open Filter Set
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Möbius transformations preserve finite-boundary convergence away from their
pole. The denominator condition says precisely that the image is finite. -/
theorem real_boundary_smul_tendsto {α : Type*} {l : Filter α}
    (g : SL(2, ℝ)) (ξ : ℝ) (hg : g 1 0 * ξ + g 1 1 ≠ 0)
    (z : α → ℍ) (hz : Tendsto (fun n => (z n : ℂ)) l (𝓝 (ξ : ℂ))) :
    Tendsto (fun n => ((g • z n : ℍ) : ℂ)) l (𝓝 (realBoundaryMobius g ξ : ℂ)) := by
  have hd : (g 1 0 : ℂ) * (ξ : ℂ) + (g 1 1 : ℂ) ≠ 0 := by exact_mod_cast hg
  have hh := ((hz.const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)).div
    ((hz.const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)) hd
  change Tendsto (fun n => ((g 0 0 : ℂ) * (z n : ℂ) + (g 0 1 : ℂ)) /
    ((g 1 0 : ℂ) * (z n : ℂ) + (g 1 1 : ℂ))) l
    (𝓝 (((g 0 0 : ℂ) * (ξ : ℂ) + (g 0 1 : ℂ)) /
      ((g 1 0 : ℂ) * (ξ : ℂ) + (g 1 1 : ℂ)))) at hh
  simpa only [UpperHalfPlane.coe_specialLinearGroup_apply, realBoundaryMobius,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    RingHom.id_apply, Algebra.algebraMap_self] using hh

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hmass in
/-- The constructed finite real Martin map intertwines Möbius transformations
with the proved action on the actual Martin boundary. -/
theorem rayMartinPoint_mobius (g : Γ) (ξ : ℝ)
    (hg : (g : SL(2, ℝ)) 1 0 * ξ + (g : SL(2, ℝ)) 1 1 ≠ 0) :
    rayMartinPoint Γ s μ hpos hgen hgap (realBoundaryMobius g ξ) =
      martinBoundaryMap s μ hpos hgen hgap 1 g (rayMartinPoint Γ s μ hpos hgen hgap ξ) := by
  let y := cocompactRaySequence Γ ξ
  let H := (rayMartinPoint Γ s μ hpos hgen hgap ξ).val
  have hp := (rayMartinCluster_harmonic Γ s μ hpos hgen hgap
    (rayMartinPoint_mem Γ s μ hpos hgen hgap ξ)).2.1
  have hy : Tendsto (fun n => (((g * y n) • UpperHalfPlane.I : ℍ) : ℂ)) atTop
      (𝓝 (realBoundaryMobius g ξ : ℂ)) := by
    have hh := real_boundary_smul_tendsto g ξ hg
      (fun n => y n • UpperHalfPlane.I) (cocompactRaySequence_tendsto Γ ξ)
    change Tendsto (fun n => ((g • (y n • UpperHalfPlane.I) : ℍ) : ℂ)) atTop
      (𝓝 (realBoundaryMobius g ξ : ℂ)) at hh
    simpa only [mul_smul] using hh
  apply Subtype.ext
  funext x
  have hlim := real_boundary_martin_tendsto Γ s μ hpos hmass hgen hgap
    (realBoundaryMobius g ξ) (fun n => g * y n) hy x
  have ht := (rayMartinPoint_tendsto Γ s μ hpos hmass hgen hgap ξ (g⁻¹ * x)).div
    (rayMartinPoint_tendsto Γ s μ hpos hmass hgen hgap ξ (g⁻¹ * 1)) (ne_of_gt (hp _))
  have he (n : ℕ) : martinQuotient s μ 1 (g⁻¹ * x) (y n) /
      martinQuotient s μ 1 (g⁻¹ * 1) (y n) = martinQuotient s μ 1 x (g * y n) :=
    congrFun (martinTranslate_embedding s μ hpos hgen hgap 1 g (y n)) x
  have ht' : Tendsto (fun n => martinQuotient s μ 1 x (g * y n)) atTop
      (𝓝 (H (g⁻¹ * x) / H (g⁻¹ * 1))) := by
    change Tendsto (fun n => martinQuotient s μ 1 (g⁻¹ * x) (y n) /
      martinQuotient s μ 1 (g⁻¹ * 1) (y n)) atTop
      (𝓝 (H (g⁻¹ * x) / H (g⁻¹ * 1))) at ht
    simpa only [he] using ht
  exact tendsto_nhds_unique hlim ht'

include hmass in
/-- The geometric Martin kernel has the expected normalized covariance formula
at all finite source and image boundary coordinates. -/
theorem rayMartinPoint_kernel_covariance (g x : Γ) (ξ : ℝ)
    (hg : (g : SL(2, ℝ)) 1 0 * ξ + (g : SL(2, ℝ)) 1 1 ≠ 0) :
    (rayMartinPoint Γ s μ hpos hgen hgap (realBoundaryMobius g ξ)).val x =
      (rayMartinPoint Γ s μ hpos hgen hgap ξ).val (g⁻¹ * x) /
        (rayMartinPoint Γ s μ hpos hgen hgap ξ).val g⁻¹ := by
  rw [rayMartinPoint_mobius Γ s μ hpos hmass hgen hgap g ξ hg]
  simp only [martinBoundaryMap, martinTranslate, mul_one]

end Singularity
