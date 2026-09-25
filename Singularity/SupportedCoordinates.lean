import Singularity.CountingSequence

/-!
# Coordinates on a supported Hilbert space

An enumeration of A gives a linear isometric equivalence from the concrete
supported subspace to sequence ℓ². The inverse is extension by zero. This permits
transport of the actual compressed Green inverse to cyclic-orbit coordinates.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology Classical

namespace Singularity

variable {X ι : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

/-- Read a supported vector in the coordinates of an enumeration of A. -/
def supportedCoordinates {A : Set X} (e : ι ≃ A) (f : supportedL2 A) : SequenceL2 ι :=
  ⟨fun i => (f : GroupL2 X) (e i), mem_sequenceL2_of_bound
    ((counting_square_summable (f : GroupL2 X)).comp_injective
      (Subtype.val_injective.comp e.injective)) (fun _ => le_rfl)⟩

omit [Countable X] in
theorem supportedCoordinates_apply {A : Set X} (e : ι ≃ A) (f : supportedL2 A) (i : ι) :
    supportedCoordinates e f i = (f : GroupL2 X) (e i) := rfl

/-- Restricting the square sum to A loses no terms. -/
theorem supported_norm_sq {A : Set X} (f : supportedL2 A) :
    ‖f‖ ^ 2 = ∑' a : A, ‖(f : GroupL2 X) a‖ ^ 2 := by
  rw [← Submodule.norm_coe, counting_norm_sq]
  symm
  apply tsum_subtype_eq_of_support_subset (f := fun x : X => ‖(f : GroupL2 X) x‖ ^ 2) (s := A)
  intro x hx
  by_contra hxa
  exact hx (by simp [f.property x hxa])

theorem supportedCoordinates_norm {A : Set X} (e : ι ≃ A) (f : supportedL2 A) :
    ‖supportedCoordinates e f‖ = ‖f‖ := by
  have h : ‖supportedCoordinates e f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [sequenceL2_norm_sq, supported_norm_sq]
    exact e.tsum_eq (fun a => ‖(f : GroupL2 X) a‖ ^ 2)
  nlinarith [norm_nonneg (supportedCoordinates e f), norm_nonneg f]

/-- Reading coordinates is a linear isometry. -/
def supportedCoordinatesIsometry {A : Set X} (e : ι ≃ A) :
    supportedL2 A →ₗᵢ[ℂ] SequenceL2 ι where
  toFun := supportedCoordinates e
  map_add' := by
    intro f g
    ext i
    exact counting_add_apply (f : GroupL2 X) (g : GroupL2 X) (e i)
  map_smul' := by
    intro c f
    ext i
    exact counting_smul_apply c (f : GroupL2 X) (e i)
  norm_map' := supportedCoordinates_norm e

/-- Extend raw coordinates by zero outside A. -/
def extendCoordinates {A : Set X} (e : ι ≃ A) (v : ι → ℂ) (x : X) : ℂ :=
  if hx : x ∈ A then v (e.symm ⟨x, hx⟩) else 0

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X] in
theorem extendCoordinates_apply {A : Set X} (e : ι ≃ A) (v : ι → ℂ) (i : ι) :
    extendCoordinates e v (e i) = v i := by
  simp [extendCoordinates]

omit [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X] in
theorem extendCoordinates_off {A : Set X} (e : ι ≃ A) (v : ι → ℂ)
    {x : X} (hx : x ∉ A) : extendCoordinates e v x = 0 := by
  simp [extendCoordinates, hx]

/-- The zero extension of a sequence ℓ² vector belongs to counting-measure L². -/
theorem extendCoordinates_memLp {A : Set X} (e : ι ≃ A) (v : SequenceL2 ι) :
    MemLp (extendCoordinates e v) 2 Measure.count := by
  have hs : Summable (fun i => ‖v i‖ ^ 2) := by
    simpa using (memℓp_gen_iff (p := 2) (by norm_num)).mp v.property
  have ha : Summable (fun a : A => ‖extendCoordinates e v a‖ ^ 2) := by
    apply e.summable_iff.mp
    simpa only [Function.comp_def, extendCoordinates_apply] using hs
  have hfull : Summable (fun x : X => ‖extendCoordinates e v x‖ ^ 2) := by
    have h := (summable_subtype_iff_indicator
      (f := fun x : X => ‖extendCoordinates e v x‖ ^ 2) (s := A)).mp ha
    convert h using 1
    ext x
    by_cases hx : x ∈ A
    · simp [hx]
    · simp [hx, extendCoordinates_off e v hx]
  exact mem_countingL2_of_bound hfull (fun _ => le_rfl)

/-- Every sequence is the coordinate image of its zero extension. -/
theorem supportedCoordinates_surjective {A : Set X} (e : ι ≃ A) :
    Function.Surjective (supportedCoordinatesIsometry e) := by
  intro v
  let f := (extendCoordinates_memLp e v).toLp (extendCoordinates e v)
  have hf (x : X) : f x = extendCoordinates e v x :=
    Measure.ae_count_iff.mp (MemLp.coeFn_toLp (extendCoordinates_memLp e v)) x
  let w : supportedL2 A := ⟨f, fun x hx => (hf x).trans (extendCoordinates_off e v hx)⟩
  refine ⟨w, ?_⟩
  ext i
  exact (hf (e i)).trans (extendCoordinates_apply e v i)

/-- The actual supported Hilbert space, isometrically identified with sequence ℓ². -/
def supportedCoordinatesEquiv {A : Set X} (e : ι ≃ A) :
    supportedL2 A ≃ₗᵢ[ℂ] SequenceL2 ι :=
  LinearIsometryEquiv.ofSurjective (supportedCoordinatesIsometry e)
    (supportedCoordinates_surjective e)

theorem supportedCoordinatesEquiv_apply {A : Set X} (e : ι ≃ A)
    (f : supportedL2 A) (i : ι) :
    supportedCoordinatesEquiv e f i = (f : GroupL2 X) (e i) := rfl

/-- Transport an actual bounded operator to the enumerated coordinates. -/
def coordinateOperator {A : Set X} (e : ι ≃ A) (M : supportedL2 A →L[ℂ] supportedL2 A) :
    SequenceL2 ι →L[ℂ] SequenceL2 ι :=
  (supportedCoordinatesEquiv e).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (M.comp (supportedCoordinatesEquiv e).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem coordinateOperator_apply {A : Set X} (e : ι ≃ A)
    (M : supportedL2 A →L[ℂ] supportedL2 A) (f : supportedL2 A) :
    coordinateOperator e M (supportedCoordinatesEquiv e f) = supportedCoordinatesEquiv e (M f) := by
  simp [coordinateOperator]

/-- Changing to isometric coordinates preserves the exact operator norm. -/
theorem coordinateOperator_norm {A : Set X} (e : ι ≃ A)
    (M : supportedL2 A →L[ℂ] supportedL2 A) : ‖coordinateOperator e M‖ = ‖M‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M)
    intro f
    change ‖supportedCoordinatesEquiv e (M ((supportedCoordinatesEquiv e).symm f))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    simpa only [LinearIsometryEquiv.norm_map] using
      M.le_opNorm ((supportedCoordinatesEquiv e).symm f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    simpa only [coordinateOperator_apply, LinearIsometryEquiv.norm_map] using
      (coordinateOperator e M).le_opNorm (supportedCoordinatesEquiv e f)

/-- The operator pairing is unchanged by passage to orbit coordinates. -/
theorem coordinateOperator_pairing {A : Set X} (e : ι ≃ A)
    (M : supportedL2 A →L[ℂ] supportedL2 A) (u v : supportedL2 A) :
    inner ℂ (supportedCoordinatesEquiv e u)
      (coordinateOperator e M (supportedCoordinatesEquiv e v)) = inner ℂ u (M v) := by
  rw [coordinateOperator_apply]
  exact (supportedCoordinatesEquiv e).inner_map_map u (M v)

/-- Dominated convergence can be checked solely on enumerated A-coordinates. -/
theorem supportedCoordinates_limit_exists {A : Set X} (e : ι ≃ A)
    {α : Type*} {l : Filter α} [l.NeBot] {u : α → supportedL2 A}
    {v : ι → ℂ} {b : ι → ℝ} (hb : Summable (fun i => b i ^ 2))
    (hbound : ∀ᶠ n in l, ∀ i, ‖(u n : GroupL2 X) (e i)‖ ≤ b i)
    (hpoint : ∀ i, Tendsto (fun n => (u n : GroupL2 X) (e i)) l (𝓝 (v i))) :
    ∃ w : supportedL2 A, (∀ i, (w : GroupL2 X) (e i) = v i) ∧ Tendsto u l (𝓝 w) := by
  obtain ⟨z, hz, ht⟩ := sequenceL2_limit_exists
    (u := fun n => supportedCoordinatesEquiv e (u n)) hb hbound hpoint
  refine ⟨(supportedCoordinatesEquiv e).symm z, ?_, ?_⟩
  · intro i
    have he := congrArg (fun f : SequenceL2 ι => f i)
      ((supportedCoordinatesEquiv e).apply_symm_apply z)
    exact he.trans (hz i)
  · simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using
      (supportedCoordinatesEquiv e).symm.continuous.continuousAt.tendsto.comp ht

end Singularity
