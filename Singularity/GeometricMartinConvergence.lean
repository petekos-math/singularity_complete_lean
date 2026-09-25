import Singularity.BoundaryMartinComparison

/-!
# Martin convergence for arbitrary finite-boundary approaches

Every pointwise Martin cluster from an approach to ξ is dominated by the
minimal ray function. Normalization makes them identical. Compactness then
proves convergence along the original sequence, without a nontangential or
bounded-distance-to-ray condition.
-/

noncomputable section
open Filter Set
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hmass hgen hgap in
/-- A normalized nonnegative harmonic function dominated by a ray cluster
function is that function, by the proved minimality theorem. -/
theorem rayMartinCluster_eq_of_harmonic_domination {ξ : ℝ} {H J : Γ → ℝ}
    (hH : H ∈ rayMartinCluster Γ s μ ξ) (hJ1 : J 1 = 1) (hJp : ∀ x, 0 ≤ J x)
    (hJh : ∀ x, ∑ g ∈ s, μ g * J (x * g) = J x) (D : ℝ) (hD : 0 < D)
    (hb : ∀ x, J x ≤ D * H x) : J = H := by
  have hH1 := (rayMartinCluster_harmonic Γ s μ hpos hgen hgap hH).1
  have hf (x : Γ) : 0 ≤ J x / D ∧ J x / D ≤ H x := by
    exact ⟨div_nonneg (hJp x) hD.le, (div_le_iff₀ hD).mpr (by
      simpa only [mul_comm D] using hb x)⟩
  have hfharm (x : Γ) : ∑ g ∈ s, μ g * (J (x * g) / D) = J x / D := by
    simp only [← mul_div_assoc, ← Finset.sum_div, hJh x]
  obtain ⟨a, _, ha⟩ := rayMartinCluster_minimal Γ s μ hpos hmass hgen hgap hH
    (fun x => J x / D) hf hfharm
  have ha1 := ha 1
  rw [hJ1, hH1, mul_one] at ha1
  have hh1 := (div_eq_iff (ne_of_gt hD)).mp ha1
  funext x
  calc
    J x = a * H x * D := (div_eq_iff (ne_of_gt hD)).mp (ha x)
    _ = (a * D) * H x := by ring
    _ = H x := by rw [← hh1, one_mul]

include hpos hmass hgen hgap in
/-- Any pointwise Martin limit from an arbitrary approach to ξ equals its ray
boundary point. -/
theorem real_boundary_martin_limit_eq (ξ : ℝ) (y : ℕ → Γ) (J : Γ → ℝ)
    (hy : Tendsto (fun n => ((y n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (ξ : ℂ)))
    (hJ : ∀ x, Tendsto (fun n => martinQuotient s μ 1 x (y n)) atTop (𝓝 (J x))) :
    J = (rayMartinPoint Γ s μ hpos hgen hgap ξ).val := by
  have hJ1 := martin_limit_base s μ hpos hgen hgap 1 y J hJ
  have hJp (x : Γ) : 0 ≤ J x := (martin_limit_pos s μ hpos hgen hgap 1 y J hJ x).le
  have hJh (x : Γ) : ∑ g ∈ s, μ g * J (x * g) = J x :=
    (martin_limit_harmonic s μ hgap 1 y J
      (real_boundary_approach_eventually_ne Γ ξ y hy) hJ x).symm
  have hH := rayMartinPoint_mem Γ s μ hpos hgen hgap ξ
  obtain ⟨C, hC, hb⟩ := real_boundary_martin_eventual_green_comparison Γ s μ hpos hmass hgen hgap
  obtain ⟨D, hD, hd⟩ := harmonic_dominated_by_ray_of_eventual_comparison Γ s μ hpos hmass hgen hgap
    hH hJ1 hJp hJh C hC (hb ξ y J hy hJ)
  exact rayMartinCluster_eq_of_harmonic_domination Γ s μ hpos hmass hgen hgap hH hJ1 hJp hJh D hD hd

include hpos hmass hgen hgap in
/-- Full pointwise Martin convergence along every sequence tending to a finite
real boundary coordinate. No restriction on the approach is imposed. -/
theorem real_boundary_martin_tendsto (ξ : ℝ) (y : ℕ → Γ)
    (hy : Tendsto (fun n => ((y n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (ξ : ℂ))) (x : Γ) :
    Tendsto (fun n => martinQuotient s μ 1 x (y n)) atTop
      (𝓝 ((rayMartinPoint Γ s μ hpos hgen hgap ξ).val x)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨J, _, _, φ, hφ, hlim⟩ := martinQuotient_subsequence s μ hpos hgen hgap 1 (y ∘ ns)
  have he := real_boundary_martin_limit_eq Γ s μ hpos hmass hgen hgap ξ
    (fun n => y (ns (φ n))) J (hy.comp (hns.comp hφ.tendsto_atTop)) hlim
  exact ⟨φ, he ▸ hlim x⟩

end Singularity
