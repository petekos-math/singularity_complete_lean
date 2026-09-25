import Singularity.ShrinkingAxisGeometry
import Singularity.GeometricEntranceIteration
import Singularity.CocompactGreenBall

/-!
# Uniform Green product comparison along hyperbolic axes

The ball sequence and its admissible pair sets are constructed here. The longer
side of the axis interval is halved at every step, and cocompactness supplies
nearby orbit centers. The resulting uniform Green product estimate has no
polynomial endpoint-distance loss. It applies when the middle orbit point is
within a fixed distance of the indicated axis segment.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Constructed shrinking orbit balls give a uniform product comparison for
all admissible axis tubes and middle points within E of the axis origin. -/
theorem axis_green_product_bound_of_orbit_cover (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (E : ℝ) (hE : 0 ≤ E) (hcover : ∀ z : ℍ, ∃ u : Γ, dist (u • UpperHalfPlane.I) z ≤ E) :
    ∃ H : ℝ, 0 < H ∧ ∀ (g : SL(2, ℝ)) (l r : ℝ), 0 ≤ l → 0 ≤ r →
      ∀ (o : Γ), dist (g • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ E →
      ∀ xy ∈ axisPairSet Γ g E (l, r),
        walkGreen s μ xy.1 xy.2 ≤ H * (walkGreen s μ xy.1 o * walkGreen s μ o xy.2) := by
  obtain ⟨Rmin, herror⟩ := entrancePairRemainder_relative_bound Γ s μ hpos hgen hgap
    (2 * Real.log 32 + 2 * E) 800 1
  let T := 1600 * (max Rmin 0 + E + Real.log 64 + Real.log 4 + Real.log 2 + 1)
  have hlog64 : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmax0 : 0 ≤ max Rmin 0 := le_max_right _ _
  have hmaxmin : Rmin ≤ max Rmin 0 := le_max_left _ _
  have hT : 0 < T := by dsimp [T]; linarith
  have hTgeom : 400 * (E + Real.log 64 + 1) ≤ T := by dsimp [T]; linarith
  have hTmin : 400 * Rmin ≤ T := by dsimp [T]; linarith
  have hT4 : 400 * Real.log 4 ≤ T := by dsimp [T]; linarith
  have hT2 : 1600 * Real.log 2 ≤ T := by dsimp [T]; linarith
  obtain ⟨H, hH, hiterate⟩ := hyperbolic_finite_entrance_iteration Γ s μ hpos hmass hgen hgap
    (2 * T + 2 * E)
  refine ⟨H, hH, ?_⟩
  intro g l r hl hr o ho
  let p := axisInterval l r
  obtain ⟨N, hstop, hbefore⟩ := exists_axisInterval_stop l r T hl hr hT
  have hp (n : ℕ) : 0 ≤ (p n).1 ∧ 0 ≤ (p n).2 := axisInterval_nonneg l r hl hr n
  choose c hc using fun n : ℕ => hcover (g • verticalHeightRay UpperHalfPlane.I (axisIntervalCut (p n)))
  let radius : ℕ → ℝ := fun n => ((p n).1 + (p n).2) / 400
  let A : ℕ → Finset Γ := fun n => (finite_hyperbolic_orbit_openBall Γ (c n) (radius n)).toFinset
  have hA (n : ℕ) : (A n : Set Γ) =
      {a : Γ | dist (a • UpperHalfPlane.I) (c n • UpperHalfPlane.I) < radius n} :=
    Set.Finite.coe_toFinset _
  have hradius : ∀ n < N, Real.log 4 + (N - 1 - n : ℕ) * Real.log 2 ≤ radius n :=
    axisInterval_radius_schedule l r T (Real.log 4) (Real.log 2) hl hr hT4 hT2 N hbefore
  have hresult := hiterate N A (fun n => axisIntervalLast (p n))
    (fun n => axisPairSet Γ g E (p n)) (fun n => Real.exp (-radius n)) o
    (fun _ _ => (Real.exp_pos _).le) (finite_radius_errors_le_half N radius hradius)
  apply hresult
  · intro n hn xy hxy a
    have ha : dist ((a : Γ) • UpperHalfPlane.I) (c n • UpperHalfPlane.I) < radius n := by
      have ha' : (a : Γ) ∈ (A n : Set Γ) := a.property
      rwa [hA n] at ha'
    exact axisPairSet_step Γ g E (p n) (hp n).1 (hp n).2 (c n) a (hc n) ha xy hxy
  · intro n hn xy hxy
    have hlarge : 400 * (E + Real.log 64 + 1) ≤ (p n).1 + (p n).2 :=
      hTgeom.trans (hbefore n hn).le
    obtain ⟨hd, hdiam, hexcess⟩ := axisPairSet_step_geometry Γ g E hE (p n)
      (hp n).1 (hp n).2 hlarge (c n) (hc n) xy hxy
    have hmin : Rmin ≤ radius n := by dsimp [radius]; linarith [hbefore n hn]
    simpa only [neg_one_mul] using herror (radius n) hmin (c n) (A n)
      (axisIntervalLast (p n)) xy (hA n) hd hdiam hexcess
  · intro xy hxy
    exact axisPairSet_terminal Γ g E T (p N) (hp N).1 (hp N).2 hstop o ho xy hxy

/-- Uniform Ancona upper bound when the middle orbit point lies within K of
a point on the axis segment joining the two endpoints. -/
theorem cocompact_axis_green_product_bound (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (K : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (g : SL(2, ℝ)) (l r : ℝ), 0 ≤ l → 0 ≤ r →
      ∀ (x o y : Γ), g • verticalHeightRay UpperHalfPlane.I (-l) = x • UpperHalfPlane.I →
      g • verticalHeightRay UpperHalfPlane.I r = y • UpperHalfPlane.I →
      dist (g • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ K →
      walkGreen s μ x y ≤ H * (walkGreen s μ x o * walkGreen s μ o y) := by
  obtain ⟨D, hD, hcover⟩ := cocompact_orbit_uniform_bound Γ
  let E := max D K
  have hE : 0 ≤ E := hD.le.trans (le_max_left _ _)
  have hcoverE : ∀ z : ℍ, ∃ u : Γ, dist (u • UpperHalfPlane.I) z ≤ E := by
    intro z
    obtain ⟨u, hu⟩ := hcover z
    exact ⟨u, hu.trans (le_max_left _ _)⟩
  obtain ⟨H, hH, hbound⟩ := axis_green_product_bound_of_orbit_cover Γ s μ hpos hmass hgen hgap E hE hcoverE
  refine ⟨H, hH, ?_⟩
  intro g l r hl hr x o y hx hy ho
  apply hbound g l r hl hr o (ho.trans (le_max_right _ _)) (x,y)
  change _ ∧ _
  rw [hx, hy, dist_self, dist_self]
  constructor <;> positivity

end Singularity
