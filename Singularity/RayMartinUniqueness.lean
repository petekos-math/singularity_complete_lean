import Singularity.RayMartinMinimality

/-!
# Uniqueness of Martin limits on each chosen cocompact ray

Ray reciprocal-Green bounds and the eventual reverse comparison give uniform
domination of any two cluster functions. Minimality and normalization then
make them equal. This does not yet address arbitrary approaches to the same
geometric boundary point or continuity in that point.
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
/-- Cluster functions on a common ray are uniformly comparable everywhere. -/
theorem cocompact_ray_martin_cluster_domination :
    ∃ D : ℝ, 0 < D ∧ ∀ (ξ : ℝ) (H J : Γ → ℝ),
      H ∈ rayMartinCluster Γ s μ ξ → J ∈ rayMartinCluster Γ s μ ξ →
      ∀ x, H x ≤ D * J x := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨C, hC, hb⟩ := cocompact_ray_martin_eventual_green_comparison Γ s μ hpos hmass hgen hgap
  obtain ⟨A, hA, ha⟩ := cocompact_ray_martin_limit_bounds Γ s μ hpos hmass hgen hgap
  let d := walkGreen s μ 1 1
  have hd : 0 < d := walkGreen_pos s μ hpos hgen hgap 1 1
  refine ⟨C * A * d ^ 2, by positivity, ?_⟩
  intro ξ H J hH hJ x
  have hJprop := rayMartinCluster_harmonic Γ s μ hpos hgen hgap hJ
  obtain ⟨φ, hφ, hφlim⟩ := hH
  obtain ⟨ψ, hψ, hψlim⟩ := hJ
  obtain ⟨n, hn⟩ := (hb ξ H ⟨φ, hφ, hφlim⟩ x).exists
  let v := cocompactRaySequence Γ ξ n
  have hHupper := (ha ξ H φ hφ hφlim n).2
  have hJlower := (ha ξ J ψ hψ hψlim n).1
  have hv := walkGreen_pos s μ hpos hgen hgap 1 v
  have hratio : H v ≤ A * d * J v := by
    have hh := (div_le_iff₀ hA).mp hJlower
    have hmul := mul_le_mul_of_nonneg_left hh hd.le
    have hh' : walkGreen s μ 1 v * H v ≤
        walkGreen s μ 1 v * (A * d * J v) := by
      change walkGreen s μ 1 v * H v ≤ d at hHupper
      change 1 ≤ walkGreen s μ 1 v * J v * A at hh
      nlinarith
    exact (mul_le_mul_iff_right₀ hv).mp hh'
  have hgreen := walkGreen_superharmonic_bound s μ hμ hmass hgap J
    (fun z => (hJprop.2.1 z).le) (fun z => (hJprop.2.2 z).le) x v
  have hdiag : walkGreen s μ v v = d := by
    simpa only [mul_one] using walkGreen_left s μ v 1 1
  rw [hdiag] at hgreen
  calc
    H x ≤ C * (walkGreen s μ x v * H v) := hn
    _ ≤ C * (walkGreen s μ x v * (A * d * J v)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio
        (walkGreen_nonneg s μ hμ x v)) hC.le
    _ = C * A * d * (walkGreen s μ x v * J v) := by ring
    _ ≤ C * A * d * (d * J x) := mul_le_mul_of_nonneg_left hgreen (by positivity)
    _ = C * A * d ^ 2 * J x := by ring

include hpos hmass hgen hgap in
/-- A finite geometric direction has at most one cluster function on its
chosen orbit ray. -/
theorem rayMartinCluster_subsingleton (ξ : ℝ) :
    (rayMartinCluster Γ s μ ξ).Subsingleton := by
  obtain ⟨D, hD, hb⟩ := cocompact_ray_martin_cluster_domination Γ s μ hpos hmass hgen hgap
  intro H hH J hJ
  have hHprop := rayMartinCluster_harmonic Γ s μ hpos hgen hgap hH
  have hJprop := rayMartinCluster_harmonic Γ s μ hpos hgen hgap hJ
  have hf (x : Γ) : 0 ≤ H x / D ∧ H x / D ≤ J x := by
    exact ⟨div_nonneg (hHprop.2.1 x).le hD.le, (div_le_iff₀ hD).mpr (by
      simpa only [mul_comm D] using hb ξ H J hH hJ x)⟩
  have hfharm (x : Γ) : ∑ g ∈ s, μ g * (H (x * g) / D) = H x / D := by
    simp only [← mul_div_assoc, ← Finset.sum_div, hHprop.2.2 x]
  obtain ⟨a, _, ha⟩ := rayMartinCluster_minimal Γ s μ hpos hmass hgen hgap hJ
    (fun x => H x / D) hf hfharm
  have ha1 := ha 1
  rw [hHprop.1, hJprop.1, mul_one] at ha1
  funext x
  have hh := (div_eq_iff (ne_of_gt hD)).mp (ha x)
  have hh1 := (div_eq_iff (ne_of_gt hD)).mp ha1
  calc
    H x = a * J x * D := hh
    _ = (a * D) * J x := by ring
    _ = J x := by rw [← hh1, one_mul]

include hpos hmass hgen hgap in
/-- Existence and uniqueness of the actual normalized ray cluster function. -/
theorem rayMartinCluster_existsUnique (ξ : ℝ) :
    ∃! H, H ∈ rayMartinCluster Γ s μ ξ := by
  obtain ⟨H, hH⟩ := rayMartinCluster_nonempty Γ s μ hpos hgen hgap ξ
  exact ⟨H, hH, fun J hJ => rayMartinCluster_subsingleton Γ s μ hpos hmass hgen hgap ξ hJ hH⟩

end Singularity
