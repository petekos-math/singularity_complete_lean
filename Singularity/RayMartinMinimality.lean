import Singularity.RayTailExcess
import Singularity.RayMartinClusters
import Singularity.HarmonicMinimality

/-!
# Minimality of the actual cocompact ray Martin limits

Ordinary Ancona comparison, the eventual small excess of geodesic rays, and
the Green superharmonic inequality suffice. No relative Ancona inequality or
assumed geometric boundary identification is used.
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

omit [DiscreteTopology Γ] in
include hpos hgen hgap in
/-- Ray cluster functions are normalized, strictly positive, and harmonic. -/
theorem rayMartinCluster_harmonic {ξ : ℝ} {H : Γ → ℝ}
    (hH : H ∈ rayMartinCluster Γ s μ ξ) :
    H 1 = 1 ∧ (∀ x, 0 < H x) ∧ (∀ x, ∑ g ∈ s, μ g * H (x * g) = H x) := by
  obtain ⟨φ, hφ, ht⟩ := hH
  refine ⟨martin_limit_base s μ hpos hgen hgap 1 _ H ht,
    martin_limit_pos s μ hpos hgen hgap 1 _ H ht, fun x => ?_⟩
  exact (martin_limit_harmonic s μ hgap 1 (fun n => cocompactRaySequence Γ ξ (φ n)) H
    (fun z => hφ.tendsto_atTop.eventually
      ((cocompactRaySequence_eventually_ne Γ ξ z).mono (fun _ h => h.symm))) ht x).symm

include hpos hmass hgen hgap in
/-- Every ray limit has a uniform reverse Green comparison on a tail.
The constant is independent of the ray, cluster function, and starting state. -/
theorem cocompact_ray_martin_eventual_green_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : ℝ) (H : Γ → ℝ), H ∈ rayMartinCluster Γ s μ ξ →
      ∀ x, ∀ᶠ n in atTop, H x ≤ C *
        (walkGreen s μ x (cocompactRaySequence Γ ξ n) * H (cocompactRaySequence Γ ξ n)) := by
  obtain ⟨C, hC, hb⟩ := cocompact_excess_green_product_bound Γ s μ hpos hmass hgen hgap
    (1 + 4 * cocompactOrbitRadius Γ)
  refine ⟨C, hC, ?_⟩
  intro ξ H hH x
  obtain ⟨φ, hφ, ht⟩ := hH
  filter_upwards [cocompactRaySequence_eventual_triangle_excess Γ ξ x] with n hn
  have he : ∀ᶠ k in atTop,
      martinQuotient s μ 1 x (cocompactRaySequence Γ ξ (φ k)) ≤
        C * (walkGreen s μ x (cocompactRaySequence Γ ξ n) *
          martinQuotient s μ 1 (cocompactRaySequence Γ ξ n) (cocompactRaySequence Γ ξ (φ k))) := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop n)] with k hk
    have hh := hb x (cocompactRaySequence Γ ξ n) (cocompactRaySequence Γ ξ (φ k)) (hn (φ k) hk)
    have hd := walkGreen_pos s μ hpos hgen hgap 1 (cocompactRaySequence Γ ξ (φ k))
    have hdiv := div_le_div_of_nonneg_right hh hd.le
    simpa only [martinQuotient, mul_div_assoc] using hdiv
  exact le_of_tendsto_of_tendsto (ht x)
    (((ht (cocompactRaySequence Γ ξ n)).const_mul
      (walkGreen s μ x (cocompactRaySequence Γ ξ n))).const_mul C) he

include hpos hmass hgen hgap in
/-- Every actual ray cluster function is minimal in the positive harmonic cone. -/
theorem rayMartinCluster_minimal {ξ : ℝ} {H : Γ → ℝ}
    (hH : H ∈ rayMartinCluster Γ s μ ξ) (f : Γ → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ H x)
    (hfharm : ∀ x, ∑ g ∈ s, μ g * f (x * g) = f x) :
    ∃ a ∈ Icc (0 : ℝ) 1, ∀ x, f x = a * H x := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨_, hHp, hHharm⟩ := rayMartinCluster_harmonic Γ s μ hpos hgen hgap hH
  obtain ⟨C, hC, hb⟩ := cocompact_ray_martin_eventual_green_comparison Γ s μ hpos hmass hgen hgap
  have hd := walkGreen_pos s μ hpos hgen hgap (1 : Γ) 1
  let c := (C * walkGreen s μ 1 1)⁻¹
  have hc : 0 < c := inv_pos.mpr (mul_pos hC hd)
  apply harmonic_minimal_of_green_minorization s μ hμ hmass hgap H hHp hHharm
    (cocompactRaySequence Γ ξ) c hc ?_ f hf hfharm
  intro x
  filter_upwards [hb ξ H hH x] with n hn
  have hdiag : walkGreen s μ (cocompactRaySequence Γ ξ n) (cocompactRaySequence Γ ξ n) =
      walkGreen s μ 1 1 := by
    simpa only [mul_one] using walkGreen_left s μ (cocompactRaySequence Γ ξ n) 1 1
  calc
    c * walkGreen s μ (cocompactRaySequence Γ ξ n) (cocompactRaySequence Γ ξ n) * H x =
        H x / C := by
      rw [hdiag]
      dsimp only [c]
      field_simp
    _ ≤ walkGreen s μ x (cocompactRaySequence Γ ξ n) * H (cocompactRaySequence Γ ξ n) :=
      (div_le_iff₀ hC).mpr (by nlinarith [hn])

end Singularity
