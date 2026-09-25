import Singularity.HittingMeasureAtoms
import Singularity.CurrentComparison
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Metrizable.Basic

/-!
# Measures on ordered distinct geometric boundary pairs

The current lives on the open complement of the diagonal in the compact
real-projective boundary square. Nonatomic probability marginals give a
probability reference measure there. A continuous real kernel gives a locally
finite, regular, sigma-finite weighted measure. No Naïm kernel is assumed to
exist merely by defining this construction.
-/

noncomputable section
open MeasureTheory Set OnePoint
open scoped Classical Topology MatrixGroups

namespace Singularity

/-- Ordered pairs of distinct points of the geometric boundary. -/
abbrev BoundaryPair := {p : OnePoint ℝ × OnePoint ℝ // p.1 ≠ p.2}

instance boundaryPair_metrizable : TopologicalSpace.MetrizableSpace BoundaryPair :=
  TopologicalSpace.MetrizableSpace.subtype {p : OnePoint ℝ × OnePoint ℝ | p.1 ≠ p.2}

/-- The distinct-pair locus is open in the compact boundary square. -/
theorem isOpen_boundaryPair : IsOpen {p : OnePoint ℝ × OnePoint ℝ | p.1 ≠ p.2} :=
  isClosed_diagonal.isOpen_compl

instance boundaryPair_locallyCompact : LocallyCompactSpace BoundaryPair :=
  isOpen_boundaryPair.locallyCompactSpace

/-- The diagonal action preserves distinct endpoints. -/
instance boundaryPairSLAction : MulAction SL(2, ℝ) BoundaryPair where
  smul g p := ⟨(g • p.val.1, g • p.val.2), fun h => p.property (MulAction.injective g h)⟩
  one_smul p := by
    apply Subtype.ext
    change ((1 : SL(2, ℝ)) • p.val.1, (1 : SL(2, ℝ)) • p.val.2) = p.val
    simp
  mul_smul g h p := by
    apply Subtype.ext
    change ((g * h) • p.val.1, (g * h) • p.val.2) = (g • (h • p.val.1), g • (h • p.val.2))
    simp only [mul_smul]

instance boundaryPairSLContinuous : ContinuousConstSMul SL(2, ℝ) BoundaryPair where
  continuous_const_smul g := by
    apply Continuous.subtype_mk
    exact ((continuous_const_smul g).comp (continuous_fst.comp continuous_subtype_val)).prodMk
      ((continuous_const_smul g).comp (continuous_snd.comp continuous_subtype_val))

/-- Restrict the product of the two actual boundary laws to the distinct-pair space. -/
def boundaryPairMeasure (μ ν : Measure (OnePoint ℝ)) : Measure BoundaryPair :=
  (μ.prod ν).comap Subtype.val

/-- Embedding the restricted product back in the square gives its restriction off the diagonal. -/
theorem boundaryPairMeasure_map (μ ν : Measure (OnePoint ℝ)) :
    Measure.map Subtype.val (boundaryPairMeasure μ ν) =
      (μ.prod ν).restrict {p : OnePoint ℝ × OnePoint ℝ | p.1 ≠ p.2} :=
  map_comap_subtype_coe isOpen_boundaryPair.measurableSet _

/-- With a nonatomic second marginal, passage to distinct pairs loses no mass. -/
theorem boundaryPairMeasure_map_eq (μ ν : Measure (OnePoint ℝ)) [SFinite ν] [NullSingletonClass ν] :
    Measure.map Subtype.val (boundaryPairMeasure μ ν) = μ.prod ν := by
  rw [boundaryPairMeasure_map]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simpa using compactBoundary_product_diagonal_null μ ν

instance boundaryPairMeasure_finite (μ ν : Measure (OnePoint ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (boundaryPairMeasure μ ν) := by unfold boundaryPairMeasure; infer_instance

/-- Products of nonatomic hitting probabilities define a probability reference measure on pairs. -/
theorem boundaryPairMeasure_probability (μ ν : Measure (OnePoint ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    IsProbabilityMeasure (boundaryPairMeasure μ ν) := by
  constructor
  have h := congrArg (fun m : Measure (OnePoint ℝ × OnePoint ℝ) => m univ)
    (boundaryPairMeasure_map_eq μ ν)
  simpa [Measure.map_apply measurable_subtype_coe MeasurableSet.univ] using h

/-- A measurable inclusion computes pair mass by the image set in the boundary square. -/
theorem boundaryPairMeasure_apply (μ ν : Measure (OnePoint ℝ)) (A : Set BoundaryPair) :
    boundaryPairMeasure μ ν A = (μ.prod ν) (Subtype.val '' A) :=
  comap_subtype_coe_apply isOpen_boundaryPair.measurableSet _ A

/-- Absolute continuity of the marginals passes to the actual distinct-pair measures. -/
theorem boundaryPairMeasure_absolutelyContinuous
    (μ μ₀ ν ν₀ : Measure (OnePoint ℝ)) [SFinite ν] [SFinite ν₀]
    (hμ : μ ≪ μ₀) (hν : ν ≪ ν₀) : boundaryPairMeasure μ ν ≪ boundaryPairMeasure μ₀ ν₀ := by
  intro A hA
  rw [boundaryPairMeasure_apply] at hA ⊢
  exact (hμ.prod hν) hA

/-- Weight the actual distinct-pair product by a real kernel. -/
def boundaryPairCurrent (μ ν : Measure (OnePoint ℝ)) (K : BoundaryPair → ℝ) : Measure BoundaryPair :=
  (boundaryPairMeasure μ ν).withDensity (fun p => ENNReal.ofReal (K p))

/-- Every finite real kernel gives a sigma-finite current, even when its total mass is infinite. -/
theorem boundaryPairCurrent_sigmaFinite (μ ν : Measure (OnePoint ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (K : BoundaryPair → ℝ) :
    SigmaFinite (boundaryPairCurrent μ ν K) := by unfold boundaryPairCurrent; infer_instance

/-- Continuity only on the off-diagonal space suffices for local finiteness of the current. -/
theorem boundaryPairCurrent_locallyFinite (μ ν : Measure (OnePoint ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (K : BoundaryPair → ℝ) (hK : Continuous K) :
    IsLocallyFiniteMeasure (boundaryPairCurrent μ ν K) :=
  IsLocallyFiniteMeasure.withDensity_ofReal hK

/-- The off-diagonal current with continuous kernel is a regular Borel measure. -/
theorem boundaryPairCurrent_regular (μ ν : Measure (OnePoint ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (K : BoundaryPair → ℝ) (hK : Continuous K) :
    Measure.Regular (boundaryPairCurrent μ ν K) := by
  let := boundaryPairCurrent_locallyFinite μ ν K hK
  exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- A positive measurable kernel preserves the reference measure class on distinct pairs. -/
theorem boundaryPairCurrent_measureClass (μ ν : Measure (OnePoint ℝ))
    (K : BoundaryPair → ℝ) (hK : Measurable K) (hp : ∀ p, 0 < K p) :
    boundaryPairCurrent μ ν K ≪ boundaryPairMeasure μ ν ∧
      boundaryPairMeasure μ ν ≪ boundaryPairCurrent μ ν K :=
  positive_real_weight_measureClass _ K hK (Filter.Eventually.of_forall hp)

/-- Marginal absolute continuity supplies the comparison with a positive reference current. -/
theorem boundaryPairCurrent_absolutelyContinuous
    (μ μ₀ ν ν₀ : Measure (OnePoint ℝ)) [SFinite ν] [SFinite ν₀]
    (hμ : μ ≪ μ₀) (hν : ν ≪ ν₀)
    (K L : BoundaryPair → ℝ) (hL : Measurable L) (hpL : ∀ p, 0 < L p) :
    boundaryPairCurrent μ ν K ≪ boundaryPairCurrent μ₀ ν₀ L :=
  (withDensity_absolutelyContinuous _ _).trans
    ((boundaryPairMeasure_absolutelyContinuous μ μ₀ ν ν₀ hμ hν).trans
      (boundaryPairCurrent_measureClass μ₀ ν₀ L hL hpL).2)

/-- Equivalent marginals and positive kernels give equivalent off-diagonal currents. -/
theorem boundaryPairCurrent_equivalent
    (μ μ₀ ν ν₀ : Measure (OnePoint ℝ)) [SFinite ν] [SFinite ν₀]
    (hμ : μ ≪ μ₀) (hμ' : μ₀ ≪ μ) (hν : ν ≪ ν₀) (hν' : ν₀ ≪ ν)
    (K L : BoundaryPair → ℝ) (hK : Measurable K) (hL : Measurable L)
    (hpK : ∀ p, 0 < K p) (hpL : ∀ p, 0 < L p) :
    boundaryPairCurrent μ ν K ≪ boundaryPairCurrent μ₀ ν₀ L ∧
      boundaryPairCurrent μ₀ ν₀ L ≪ boundaryPairCurrent μ ν K :=
  ⟨boundaryPairCurrent_absolutelyContinuous μ μ₀ ν ν₀ hμ hν K L hL hpL,
    boundaryPairCurrent_absolutelyContinuous μ₀ μ ν₀ ν hμ' hν' L K hK hpK⟩

/-- A positive kernel over probability marginals gives a nonzero current. -/
theorem boundaryPairCurrent_ne_zero (μ ν : Measure (OnePoint ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (K : BoundaryPair → ℝ) (hK : Measurable K) (hp : ∀ p, 0 < K p) :
    boundaryPairCurrent μ ν K ≠ 0 := by
  let := boundaryPairMeasure_probability μ ν
  exact positive_real_weight_ne_zero _ K hK (Filter.Eventually.of_forall hp)

end Singularity
