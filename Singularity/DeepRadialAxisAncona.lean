import Singularity.ShrinkingRadialDepth
import Singularity.RelativeEntranceIteration
import Singularity.DeepRadialRelativeDetour
import Singularity.GeometricEntranceIteration
import Singularity.CocompactGreenBall

/-!
# Constructed relative Ancona comparison with linear radial clearance

The actual shrinking orbit balls are constructed, and every depth, successor,
relative-error, and terminal condition is discharged. A buffer proportional
to the initial interval length keeps all admissible tubes inside the deep
radial region. The resulting comparison constant is independent of length.
This additional clearance is explicit and is stronger than the final barrier
comparison needed for strong Ancona.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Uniform relative Ancona from the constructed shrinking-ball sequence,
under a linear clearance allowance for all intermediate endpoint tubes. -/
theorem radial_axis_product_bound_of_orbit_cover
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (E : ℝ) (hE : 0 ≤ E) (hcover : ∀ z : ℍ, ∃ u : Γ, dist (u • UpperHalfPlane.I) z ≤ E) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ (q g : SL(2, ℝ)) (a l r : ℝ), 0 ≤ l → 0 ≤ r →
      a+H+(l+r)/50+E ≤ axisRadialCoordinate (q • (g • verticalHeightRay UpperHalfPlane.I (-l))) →
      a+H+(l+r)/50+E ≤ axisRadialCoordinate (q • (g • verticalHeightRay UpperHalfPlane.I r)) →
      ∀ o : Γ, dist (g • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ E →
      ∀ xy ∈ axisPairSet Γ g E (l,r),
        killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I a) xy.1 xy.2 ≤
          C * (killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I a) xy.1 o *
            killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I a) o xy.2) := by
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  obtain ⟨Hd,Rmin,hHd,herror⟩ := cocompact_deep_radial_relative_green_detour Γ s μ hpos hmass hgen hgap
    (2*Real.log 32+2*E) 800 1
  let T := 1600*(max Rmin 0+E+Real.log 64+Real.log 4+Real.log 2+1)
  have hlog64 : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmax0 : 0 ≤ max Rmin 0 := le_max_right _ _
  have hmaxmin : Rmin ≤ max Rmin 0 := le_max_left _ _
  have hT : 0 < T := by dsimp [T]; linarith
  have hTgeom : 400*(E+Real.log 64+1) ≤ T := by dsimp [T]; linarith
  have hTmin : 400*Rmin ≤ T := by dsimp [T]; linarith
  have hT4 : 400*Real.log 4 ≤ T := by dsimp [T]; linarith
  have hT2 : 1600*Real.log 2 ≤ T := by dsimp [T]; linarith
  obtain ⟨Ht,C,hHt,hC,hterminal⟩ := radial_near_center_killedGreen_product_bound Γ s μ hpos hmass hgen hgap (2*T+2*E)
  let H := max Hd Ht
  refine ⟨H,2*C,hHd.trans_le (le_max_left _ _),by positivity,?_⟩
  intro q g a l r hl hr hleft hright o ho
  let A := radialOrbitSublevel Γ q UpperHalfPlane.I a
  let p := axisInterval l r
  obtain ⟨N,hstop,hbefore⟩ := exists_axisInterval_stop l r T hl hr hT
  have hp (n : ℕ) : 0 ≤ (p n).1 ∧ 0 ≤ (p n).2 := axisInterval_nonneg l r hl hr n
  have hdepth (n : ℕ) (xy : Γ × Γ) (hxy : xy ∈ axisPairSet Γ g E (p n)) :=
    axisPairSet_radial_depth Γ g q E l r a H hl hr hleft hright n xy hxy
  have hoDepth : a+Ht ≤ axisRadialCoordinate (q • (o • UpperHalfPlane.I)) := by
    have hmid := axisRadialCoordinate_segment_lower (q*g) (a+H+(l+r)/50+E) (-l) r 0
      (by linarith) hr (by simpa only [mul_smul] using hleft) (by simpa only [mul_smul] using hright)
    simp only [verticalHeightRay_zero, mul_smul] at hmid
    have hd := axisRadialCoordinate_dist_le (q • (o • UpperHalfPlane.I)) (q • (g • UpperHalfPlane.I))
    rw [dist_smul, dist_comm (o • UpperHalfPlane.I)] at hd
    have hh := (abs_le.mp (hd.trans ho)).1
    have hHtH : Ht ≤ H := le_max_right _ _
    linarith
  choose c hc using fun n : ℕ => hcover (g • verticalHeightRay UpperHalfPlane.I (axisIntervalCut (p n)))
  let radius : ℕ → ℝ := fun n => ((p n).1+(p n).2)/400
  let B : ℕ → Finset Γ := fun n => (finite_hyperbolic_orbit_openBall Γ (c n) (radius n)).toFinset
  have hB (n : ℕ) : (B n : Set Γ) =
      {v : Γ | dist (v • UpperHalfPlane.I) (c n • UpperHalfPlane.I) < radius n} := Set.Finite.coe_toFinset _
  have hradius : ∀ n < N, Real.log 4+(N-1-n : ℕ)*Real.log 2 ≤ radius n :=
    axisInterval_radius_schedule l r T (Real.log 4) (Real.log 2) hl hr hT4 hT2 N hbefore
  apply relative_finite_entrance_iteration_bound s μ hμ hmass hgap A N B
    (fun n => axisIntervalLast (p n)) (fun n => axisPairSet Γ g E (p n))
    (fun n => Real.exp (-radius n)) o C hC.le
    (fun _ _ => (Real.exp_pos _).le) (finite_radius_errors_le_half N radius hradius)
  · intro n hn xy hxy v
    have hv : dist ((v : Γ) • UpperHalfPlane.I) (c n • UpperHalfPlane.I) < radius n := by
      have hv' : (v : Γ) ∈ (B n : Set Γ) := v.property
      rwa [hB n] at hv'
    exact axisPairSet_step Γ g E (p n) (hp n).1 (hp n).2 (c n) v (hc n) hv xy hxy
  · intro n hn xy hxy
    have hlarge : 400*(E+Real.log 64+1) ≤ (p n).1+(p n).2 := hTgeom.trans (hbefore n hn).le
    obtain ⟨hd,hdiam,hexcess⟩ := axisPairSet_step_geometry Γ g E hE (p n)
      (hp n).1 (hp n).2 hlarge (c n) (hc n) xy hxy
    have hmin : Rmin ≤ radius n := by dsimp [radius]; linarith [hbefore n hn]
    have hxydepth := hdepth n xy hxy
    have hHdH : Hd ≤ H := le_max_left _ _
    rw [hB n]
    simpa only [neg_one_mul] using herror (radius n) hmin q a (c n) xy.1 xy.2
      (by linarith [hxydepth.1]) (by linarith [hxydepth.2]) hd hdiam hexcess
  · intro xy hxy
    have hxydepth := hdepth N xy hxy
    have hHtH : Ht ≤ H := le_max_right _ _
    exact hterminal q a xy.1 o xy.2
      (axisPairSet_terminal Γ g E T (p N) (hp N).1 (hp N).2 hstop o ho xy hxy)
      (by linarith [hxydepth.1]) hoDepth

/-- A uniform Ancona upper bound for actual segment endpoints with a radial
buffer consisting of a fixed constant plus one fiftieth of segment length.
The orbit-cover and every finite iteration condition are discharged. -/
theorem cocompact_radial_axis_ancona_with_clearance
    (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (K : ℝ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ (q g : SL(2, ℝ)) (a l r : ℝ), 0 ≤ l → 0 ≤ r →
      ∀ x o y : Γ,
      g • verticalHeightRay UpperHalfPlane.I (-l) = x • UpperHalfPlane.I →
      g • verticalHeightRay UpperHalfPlane.I r = y • UpperHalfPlane.I →
      dist (g • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ K →
      a+H+(l+r)/50 ≤ axisRadialCoordinate (q • (x • UpperHalfPlane.I)) →
      a+H+(l+r)/50 ≤ axisRadialCoordinate (q • (y • UpperHalfPlane.I)) →
      killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I a) x y ≤
        C * (killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I a) x o *
          killedGreen s μ (radialOrbitSublevel Γ q UpperHalfPlane.I a) o y) := by
  obtain ⟨D,hD,hcover⟩ := cocompact_orbit_uniform_bound Γ
  let E := max D K
  have hE : 0 ≤ E := hD.le.trans (le_max_left _ _)
  have hcoverE : ∀ z : ℍ, ∃ u : Γ, dist (u • UpperHalfPlane.I) z ≤ E := by
    intro z
    obtain ⟨u,hu⟩ := hcover z
    exact ⟨u,hu.trans (le_max_left _ _)⟩
  obtain ⟨H,C,hH,hC,hbound⟩ := radial_axis_product_bound_of_orbit_cover Γ s μ hpos hmass hgen hgap E hE hcoverE
  refine ⟨H+E,C,by positivity,hC,?_⟩
  intro q g a l r hl hr x o y hx hy ho hxd hyd
  apply hbound q g a l r hl hr
    (by rw [hx]; linarith) (by rw [hy]; linarith) o (ho.trans (le_max_right _ _)) (x,y)
  change _ ∧ _
  rw [hx,hy,dist_self,dist_self]
  constructor <;> positivity

end Singularity
