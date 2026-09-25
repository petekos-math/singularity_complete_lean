import Singularity.BoundaryRayApproach
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction

/-!
# Ray approximations from compactness of the orbit quotient

Compactness of Γ\ℍ supplies a compact covering set, hence a uniform bound
from every interior point to the orbit Γ·i. Choosing points near integer ray
times constructs the group sequences used in the boundary estimates.
-/

noncomputable section
open Set Filter
open scoped MatrixGroups UpperHalfPlane Topology Classical

namespace Singularity

/-- Compactness of the actual orbit quotient gives a compact covering set. -/
theorem exists_compact_orbit_cover (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    ∃ K : Set ℍ, IsCompact K ∧ ∀ z : ℍ, ∃ g : Γ, g • z ∈ K := by
  let π : ℍ → Quotient (MulAction.orbitRel Γ ℍ) := Quotient.mk _
  have hop : IsOpenMap π := MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  have hcover : (univ : Set (Quotient (MulAction.orbitRel Γ ℍ))) ⊆
      ⋃ w : ℍ, π '' Metric.ball w 1 := by
    intro q _
    induction q using Quotient.inductionOn with
    | h z =>
      exact mem_iUnion.mpr ⟨z, z, Metric.mem_ball_self (by norm_num), rfl⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun w : ℍ => π '' Metric.ball w 1) (fun w => hop _ Metric.isOpen_ball) hcover
  refine ⟨⋃ w ∈ F, Metric.closedBall w 1,
    F.isCompact_biUnion (fun _ _ => isCompact_closedBall _ _), ?_⟩
  intro z
  obtain ⟨w, hw⟩ := mem_iUnion.mp (hF (mem_univ (π z)))
  obtain ⟨hwF, hv⟩ := mem_iUnion.mp hw
  obtain ⟨v, hvball, hvq⟩ := hv
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hvq))
  refine ⟨g, ?_⟩
  rw [hg]
  exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨hwF, Metric.ball_subset_closedBall hvball⟩⟩

/-- A compact covering set gives a uniform distance bound to any orbit. -/
theorem compact_orbit_cover_uniform_bound (Γ : Subgroup SL(2, ℝ)) (o : ℍ)
    {K : Set ℍ} (hK : IsCompact K) (hcover : ∀ z : ℍ, ∃ g : Γ, g • z ∈ K) :
    ∃ D : ℝ, 0 < D ∧ ∀ z : ℍ, ∃ g : Γ, dist (g • o) z ≤ D := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image (continuous_const.dist continuous_id).continuousOn
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro z
  obtain ⟨g, hg⟩ := hcover z
  refine ⟨g⁻¹, ?_⟩
  have hd : dist o (g • z) ≤ B := hB ⟨g • z, hg, rfl⟩
  have he : dist (g⁻¹ • o) z = dist o (g • z) := by
    change dist (((g⁻¹ : Γ) : SL(2, ℝ)) • o) z = _
    rw [← dist_smul (g : SL(2, ℝ))]
    simp
    rfl
  rw [he]
  exact hd.trans (by linarith [le_max_left B 0])

/-- The orbit of i is uniformly dense in the hyperbolic metric for a compact quotient. -/
theorem cocompact_orbit_uniform_bound (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    ∃ D : ℝ, 0 < D ∧ ∀ z : ℍ, ∃ g : Γ, dist (g • UpperHalfPlane.I) z ≤ D := by
  obtain ⟨K, hK, hcover⟩ := exists_compact_orbit_cover Γ
  exact compact_orbit_cover_uniform_bound Γ UpperHalfPlane.I hK hcover

/-- Compact quotient supplies group sequences at uniformly bounded distance
from integer-time rays, with the same bound for every finite endpoint. -/
theorem cocompact_ray_approximations (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))] :
    ∃ D : ℝ, 0 < D ∧ ∀ ξ : ℝ, ∃ x : ℕ → Γ,
      ∀ n, dist (x n • UpperHalfPlane.I) (finiteBoundaryRay ξ (n : ℝ)) ≤ D := by
  obtain ⟨D, hD, hcover⟩ := cocompact_orbit_uniform_bound Γ
  refine ⟨D, hD, fun ξ => ?_⟩
  choose x hx using fun n : ℕ => hcover (finiteBoundaryRay ξ (n : ℝ))
  exact ⟨x, hx⟩

variable (Γ : Subgroup SL(2, ℝ)) [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]

/-- A single positive approximation radius for the whole cocompact orbit. -/
def cocompactOrbitRadius : ℝ := (cocompact_orbit_uniform_bound Γ).choose

theorem cocompactOrbitRadius_pos : 0 < cocompactOrbitRadius Γ :=
  (cocompact_orbit_uniform_bound Γ).choose_spec.1

/-- Every interior point has a nearby orbit point at the chosen radius. -/
theorem exists_cocompactOrbit_near (z : ℍ) :
    ∃ g : Γ, dist (g • UpperHalfPlane.I) z ≤ cocompactOrbitRadius Γ :=
  (cocompact_orbit_uniform_bound Γ).choose_spec.2 z

/-- Chosen group vertices near successive integer-time points on the ray. -/
def cocompactRaySequence (ξ : ℝ) (n : ℕ) : Γ :=
  (exists_cocompactOrbit_near Γ (finiteBoundaryRay ξ (n : ℝ))).choose

theorem cocompactRaySequence_bound (ξ : ℝ) (n : ℕ) :
    dist (cocompactRaySequence Γ ξ n • UpperHalfPlane.I) (finiteBoundaryRay ξ (n : ℝ)) ≤
      cocompactOrbitRadius Γ :=
  (exists_cocompactOrbit_near Γ (finiteBoundaryRay ξ (n : ℝ))).choose_spec

/-- The chosen orbit sequence converges to its prescribed finite boundary point. -/
theorem cocompactRaySequence_tendsto (ξ : ℝ) :
    Tendsto (fun n => ((cocompactRaySequence Γ ξ n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (ξ : ℂ)) :=
  near_finiteBoundaryRay_tendsto ξ (cocompactOrbitRadius Γ) (fun n : ℕ => (n : ℝ))
    tendsto_natCast_atTop_atTop (fun n => cocompactRaySequence Γ ξ n • UpperHalfPlane.I)
    (cocompactRaySequence_bound Γ ξ)

/-- The chosen sequence escapes to infinite hyperbolic distance. -/
theorem cocompactRaySequence_dist_tendsto (ξ : ℝ) :
    Tendsto (fun n => dist UpperHalfPlane.I (cocompactRaySequence Γ ξ n • UpperHalfPlane.I))
      atTop atTop :=
  near_finiteBoundaryRay_dist_tendsto ξ (cocompactOrbitRadius Γ) (fun n : ℕ => (n : ℝ))
    tendsto_natCast_atTop_atTop (fun n => Nat.cast_nonneg n)
    (fun n => cocompactRaySequence Γ ξ n • UpperHalfPlane.I) (cocompactRaySequence_bound Γ ξ)

/-- Each fixed group vertex is eventually avoided by the chosen sequence. -/
theorem cocompactRaySequence_eventually_ne (ξ : ℝ) (g : Γ) :
    ∀ᶠ n in atTop, cocompactRaySequence Γ ξ n ≠ g := by
  filter_upwards [(cocompactRaySequence_dist_tendsto Γ ξ).eventually_ne_atTop
    (dist UpperHalfPlane.I (g • UpperHalfPlane.I))] with n hn
  intro he
  exact hn (by rw [he])

/-- Nonzero endpoints eventually lie outside every fixed strip. -/
theorem cocompactRaySequence_eventually_outside {ξ : ℝ} (hξ : ξ ≠ 0) (R : ℝ) :
    ∀ᶠ n in atTop, cocompactRaySequence Γ ξ n • UpperHalfPlane.I ∉ axisRatioStrip R :=
  near_finiteBoundaryRay_eventually_outside_strip hξ (cocompactOrbitRadius Γ) R
    (fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop
    (fun n => cocompactRaySequence Γ ξ n • UpperHalfPlane.I) (cocompactRaySequence_bound Γ ξ)

/-- Opposite finite endpoints yield eventually opposite orbit vertices. -/
theorem cocompactRaySequence_eventually_opposite {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η) :
    ∀ᶠ n in atTop, (cocompactRaySequence Γ ξ n • UpperHalfPlane.I).re < 0 ∧
      0 ≤ (cocompactRaySequence Γ η n • UpperHalfPlane.I).re := by
  have hx := near_finiteBoundaryRay_eventually_negative hξ (cocompactOrbitRadius Γ)
    (fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop
    (fun n => cocompactRaySequence Γ ξ n • UpperHalfPlane.I) (cocompactRaySequence_bound Γ ξ)
  have hy := near_finiteBoundaryRay_eventually_positive hη (cocompactOrbitRadius Γ)
    (fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop
    (fun n => cocompactRaySequence Γ η n • UpperHalfPlane.I) (cocompactRaySequence_bound Γ η)
  filter_upwards [hx, hy] with n hn hm
  exact ⟨hn, hm.le⟩

end Singularity
