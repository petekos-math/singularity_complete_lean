import Singularity.CoordinateBarrier
import Singularity.RadialCoordinate

/-!
# Actual semicircular barriers for the group walk

We construct the stopping set and intermediate layer from log-radius in an
arbitrary isometric chart. Finite support supplies the layer width; a strict
gap proves interception without any probabilistic or geometric assumptions.
Only the relative Green comparison remains input to the harmonic comparison.
-/

noncomputable section
open MeasureTheory
open scoped Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Orbit points on the lower side of a geodesic semicircle in the q-chart. -/
def radialOrbitSublevel (Γ : Subgroup SL(2, ℝ)) (q : SL(2, ℝ)) (z : ℍ) (r : ℝ) : Set Γ :=
  {x | axisRadialCoordinate (q • (x • z)) ≤ r}

/-- The closed layer between two semicircles, of one-jump width. -/
def radialOrbitLayer (Γ : Subgroup SL(2, ℝ)) (s : Finset Γ) (q : SL(2, ℝ)) (z : ℍ)
    (t : ℝ) : Set Γ :=
  {x | t ≤ axisRadialCoordinate (q • (x • z)) ∧
    axisRadialCoordinate (q • (x • z)) ≤ t + finiteJumpLengthBound Γ z s}

/-- These actual layers separate all finite permitted jump paths across them. -/
theorem radialOrbitLayer_separates (Γ : Subgroup SL(2, ℝ)) (s : Finset Γ)
    (q : SL(2, ℝ)) (z : ℍ) (t : ℝ) (x y : Γ)
    (hx : t + finiteJumpLengthBound Γ z s < axisRadialCoordinate (q • (x • z)))
    (hy : axisRadialCoordinate (q • (y • z)) < t) :
    SeparatesJumpPaths s (radialOrbitLayer Γ s q z t) x y := by
  exact bounded_coordinate_layer_separates s (fun g => axisRadialCoordinate (q • (g • z)))
    (finiteJumpLengthBound Γ z s) t (finiteJumpLengthBound_nonneg Γ z s)
    (fun x g hg => axisRadialCoordinate_jump_bound Γ s q z x g hg)
    (radialOrbitLayer Γ s q z t) (fun _ h₁ h₂ => ⟨h₁,h₂⟩) x y hx hy

variable (Γ : Subgroup SL(2, ℝ)) [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (q : SL(2, ℝ)) (z : ℍ) (r t : ℝ)

include hμ hmass hgap in
/-- A separated outer layer intercepts first entrance into the inner half-plane. -/
theorem radialOrbitLayer_intercepts_entrance
    (hmargin : r + finiteJumpLengthBound Γ z s < t) (x : Γ)
    (hx : t + finiteJumpLengthBound Γ z s < axisRadialCoordinate (q • (x • z)))
    {a : Γ} (ha : a ∈ radialOrbitSublevel Γ q z r) :
    firstEntranceKernel s μ (radialOrbitSublevel Γ q z r ∪ radialOrbitLayer Γ s q z t) x a = 0 := by
  exact firstEntrance_eq_zero_of_coordinate_barrier s μ hμ hmass hgap
    (fun g => axisRadialCoordinate (q • (g • z))) (finiteJumpLengthBound Γ z s) r t
    (finiteJumpLengthBound_nonneg Γ z s)
    (fun x g hg => axisRadialCoordinate_jump_bound Γ s q z x g hg)
    (radialOrbitSublevel Γ q z r) (radialOrbitLayer Γ s q z t)
    (fun _ ha => ha) (fun _ h₁ h₂ => ⟨h₁,h₂⟩) hmargin x hx ha

include hμ hmass hgap in
/-- The verified boundary comparison specialized to explicit semicircular domains.
The unproved analytic input is exactly the displayed relative Green row bound. -/
theorem radialOrbitLayer_harmonic_comparison
    (hmargin : r + finiteJumpLengthBound Γ z s < t) (x o : Γ)
    (hx : t + finiteJumpLengthBound Γ z s < axisRadialCoordinate (q • (x • z)))
    (ho : t + finiteJumpLengthBound Γ z s < axisRadialCoordinate (q • (o • z)))
    (f : Γ → ℝ) (hf : MemLp (fun x => (f x : ℂ)) 2 Measure.count)
    (hharm : ∀ x, x ∉ radialOrbitSublevel Γ q z r → f x = ∑ g ∈ s, μ g * f (x*g))
    (hboundary : ∀ a ∈ radialOrbitSublevel Γ q z r, 0 ≤ f a) (lower upper : ℝ)
    (hcompare : ∀ b ∈ radialOrbitLayer Γ s q z t,
      lower * killedGreen s μ (radialOrbitSublevel Γ q z r) o b ≤
        killedGreen s μ (radialOrbitSublevel Γ q z r) x b ∧
      killedGreen s μ (radialOrbitSublevel Γ q z r) x b ≤
        upper * killedGreen s μ (radialOrbitSublevel Γ q z r) o b) :
    lower * f o ≤ f x ∧ f x ≤ upper * f o := by
  exact harmonic_comparison_of_coordinate_barrier s μ hμ hmass hgap
    (fun g => axisRadialCoordinate (q • (g • z))) (finiteJumpLengthBound Γ z s) r t
    (finiteJumpLengthBound_nonneg Γ z s)
    (fun x g hg => axisRadialCoordinate_jump_bound Γ s q z x g hg)
    (radialOrbitSublevel Γ q z r) (radialOrbitLayer Γ s q z t)
    (fun _ ha => ha) (fun _ h₁ h₂ => ⟨h₁,h₂⟩) hmargin x o hx ho f hf hharm hboundary
    lower upper (fun b hb => hcompare b hb.1)

end Singularity
