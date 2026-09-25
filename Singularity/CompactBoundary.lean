import Singularity.ProjectiveMobius
import Singularity.MobiusMeasureAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# The compact real boundary inside the Riemann sphere

The real boundary is ℝ ∪ {∞}, with the genuine projective action at every
point. The ambient compactification ℂ ∪ {∞} also contains the upper half-plane.
Both carry their Borel structures and metrizable compact Hausdorff topology.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint TopologicalSpace
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Use the Borel measurable structure on a one-point compactification. -/
instance projectiveBorelMeasurableSpace (K : Type*) [TopologicalSpace K] :
    MeasurableSpace (OnePoint K) := borel (OnePoint K)

instance projectiveBorelSpace (K : Type*) [TopologicalSpace K] : BorelSpace (OnePoint K) := ⟨rfl⟩

/-- The real projective line is metrizable, via its homeomorphism with the circle. -/
instance realProjectiveMetrizable : MetrizableSpace (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).isEmbedding.metrizableSpace

/-- The complex projective line is metrizable, via its homeomorphism with the two-sphere. -/
instance complexProjectiveMetrizable : MetrizableSpace (OnePoint ℂ) :=
  (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)).isEmbedding.metrizableSpace

/-- Real special linear matrices act on a real-algebra projective line. -/
instance projectiveSLAction (K : Type*) [Field K] [Algebra ℝ K] :
    MulAction SL(2, ℝ) (OnePoint K) :=
  MulAction.compHom (OnePoint K) (Matrix.SpecialLinearGroup.mapGL K)

instance projectiveSLContinuous (K : Type*) [NontriviallyNormedField K] [ProperSpace K]
    [Algebra ℝ K] : ContinuousConstSMul SL(2, ℝ) (OnePoint K) where
  continuous_const_smul g := continuous_projectiveMobius (Matrix.SpecialLinearGroup.mapGL K g)

instance projectiveSubgroupContinuous (K : Type*) [NontriviallyNormedField K] [ProperSpace K]
    [Algebra ℝ K] (Γ : Subgroup SL(2, ℝ)) : ContinuousConstSMul Γ (OnePoint K) where
  continuous_const_smul g := continuous_const_smul (g : SL(2, ℝ))

/-- At a finite non-pole, the compact action agrees with the existing real-chart formula. -/
theorem compactBoundary_smul_finite (g : SL(2, ℝ)) (u : ℝ)
    (hu : g 1 0 * u + g 1 1 ≠ 0) :
    g • (u : OnePoint ℝ) = (realBoundaryMobius g u : OnePoint ℝ) := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ g) • (u : OnePoint ℝ) = _
  rw [OnePoint.smul_some_eq_ite]
  change (if g 1 0 * u + g 1 1 = 0 then (∞ : OnePoint ℝ) else
    ((g 0 0 * u + g 0 1) / (g 1 0 * u + g 1 1) : ℝ)) = _
  rw [ite_eq_right hu]
  rfl

/-- The compact action sends a real-chart pole to infinity. -/
theorem compactBoundary_smul_pole (g : SL(2, ℝ)) (u : ℝ)
    (hu : g 1 0 * u + g 1 1 = 0) : g • (u : OnePoint ℝ) = ∞ := by
  change (Matrix.SpecialLinearGroup.mapGL ℝ g) • (u : OnePoint ℝ) = _
  rw [OnePoint.smul_some_eq_ite]
  change (if g 1 0 * u + g 1 1 = 0 then (∞ : OnePoint ℝ) else _) = ∞
  rw [ite_eq_left hu]

/-- Include the upper half-plane into the ambient compact sphere. -/
def hyperbolicCompactEmbedding (z : ℍ) : OnePoint ℂ := (z : ℂ)

theorem isOpenEmbedding_hyperbolicCompactEmbedding :
    Topology.IsOpenEmbedding hyperbolicCompactEmbedding :=
  OnePoint.isOpenEmbedding_coe.comp UpperHalfPlane.isOpenEmbedding_coe

/-- The compact sphere action extends the actual upper-half-plane action. -/
theorem hyperbolicCompactEmbedding_smul (g : SL(2, ℝ)) (z : ℍ) :
    hyperbolicCompactEmbedding (g • z) = g • hyperbolicCompactEmbedding z := by
  change (((g • z : ℍ) : ℂ) : OnePoint ℂ) =
    (Matrix.SpecialLinearGroup.mapGL ℂ g) • ((z : ℂ) : OnePoint ℂ)
  rw [OnePoint.smul_some_eq_ite]
  have hd : (g 1 0 : ℂ) * (z : ℂ) + (g 1 1 : ℂ) ≠ 0 :=
    UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.toGL g) z
  change (((g • z : ℍ) : ℂ) : OnePoint ℂ) =
    if (g 1 0 : ℂ) * (z : ℂ) + (g 1 1 : ℂ) = 0 then ∞ else _
  rw [ite_eq_right hd]
  congr 1
  exact UpperHalfPlane.coe_specialLinearGroup_apply g z

/-- The real projective boundary embeds in the complex sphere. -/
def compactBoundaryEmbedding : OnePoint ℝ → OnePoint ℂ := OnePoint.map Complex.ofReal

theorem continuous_compactBoundaryEmbedding : Continuous compactBoundaryEmbedding := by
  apply OnePoint.continuous_map Complex.continuous_ofReal
  simpa only [coclosedCompact_eq_cocompact] using
    Complex.isometry_ofReal.isClosedEmbedding.tendsto_cocompact

/-- Boundary inclusion commutes with every real special linear transformation. -/
theorem compactBoundaryEmbedding_smul (g : SL(2, ℝ)) (p : OnePoint ℝ) :
    compactBoundaryEmbedding (g • p) = g • compactBoundaryEmbedding p := by
  exact OnePoint.map_smul Complex.ofRealHom (Matrix.SpecialLinearGroup.mapGL ℝ g) p

/-- The finite points on the boundary have zero imaginary part; infinity is also included. -/
def compactHyperbolicBoundary : Set (OnePoint ℂ) :=
  {p | ∀ z : ℂ, p = (z : OnePoint ℂ) → z.im = 0}

theorem compactHyperbolicBoundary_infty : (∞ : OnePoint ℂ) ∈ compactHyperbolicBoundary := by
  intro z h
  exact (OnePoint.infty_ne_coe z h).elim

theorem compactHyperbolicBoundary_coe (z : ℂ) :
    (z : OnePoint ℂ) ∈ compactHyperbolicBoundary ↔ z.im = 0 := by
  simp [compactHyperbolicBoundary]

theorem isClosed_compactHyperbolicBoundary : IsClosed compactHyperbolicBoundary := by
  apply (OnePoint.isClosed_iff_of_mem compactHyperbolicBoundary_infty).mpr
  change IsClosed {z : ℂ | (z : OnePoint ℂ) ∈ compactHyperbolicBoundary}
  simp only [compactHyperbolicBoundary_coe]
  exact isClosed_eq Complex.continuous_im continuous_const

/-- The geometric boundary is compact in the ambient sphere. -/
theorem isCompact_compactHyperbolicBoundary : IsCompact compactHyperbolicBoundary :=
  isClosed_compactHyperbolicBoundary.isCompact

/-- The geometric boundary is precisely the embedded real projective line. -/
theorem compactBoundaryEmbedding_range :
    range compactBoundaryEmbedding = compactHyperbolicBoundary := by
  ext p
  cases p with
  | infty =>
    constructor
    · intro _; exact compactHyperbolicBoundary_infty
    · intro _; exact ⟨∞, rfl⟩
  | coe z =>
    rw [compactHyperbolicBoundary_coe]
    constructor
    · rintro ⟨p, hp⟩
      cases p with
      | infty => exact (OnePoint.infty_ne_coe z hp).elim
      | coe x =>
        change ((x : ℂ) : OnePoint ℂ) = (z : OnePoint ℂ) at hp
        have hz := OnePoint.coe_injective hp
        rw [← hz]
        exact Complex.ofReal_im x
    · intro hz
      refine ⟨(z.re : OnePoint ℝ), ?_⟩
      change ((z.re : ℂ) : OnePoint ℂ) = (z : OnePoint ℂ)
      congr 1
      exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using hz.symm)

/-- Boundary inclusion is injective. -/
theorem compactBoundaryEmbedding_injective : Function.Injective compactBoundaryEmbedding := by
  intro p q hpq
  cases p <;> cases q <;> simp_all [compactBoundaryEmbedding]

/-- The compact real boundary is invariant under the genuine sphere action. -/
theorem compactHyperbolicBoundary_smul (g : SL(2, ℝ)) {p : OnePoint ℂ}
    (hp : p ∈ compactHyperbolicBoundary) : g • p ∈ compactHyperbolicBoundary := by
  rw [← compactBoundaryEmbedding_range] at hp ⊢
  obtain ⟨q, rfl⟩ := hp
  exact ⟨g • q, compactBoundaryEmbedding_smul g q⟩

end Singularity
