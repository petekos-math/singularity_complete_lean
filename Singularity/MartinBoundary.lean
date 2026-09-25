import Singularity.MartinCompactness

/-!
# The concrete Martin compactification and its harmonic boundary

The compactification is the closure, in pointwise topology, of the actual
normalized Green columns. The embedding is injective. Its complement in the
closure is exactly the set of harmonic functions in that closure and is compact.
No identification with a Fuchsian geometric boundary is made here.
-/

noncomputable section
open Filter Set
open scoped Topology Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The actual normalized Green column as a point of the function space. -/
def martinEmbedding (s : Finset Γ) (μ : Γ → ℝ) (o y : Γ) : Γ → ℝ :=
  fun z => martinQuotient s μ o z y

/-- Closure in the topology of pointwise convergence. -/
def martinClosure (s : Finset Γ) (μ : Γ → ℝ) (o : Γ) : Set (Γ → ℝ) :=
  closure (Set.range (martinEmbedding s μ o))

/-- The abstract Martin boundary excludes the embedded finite states. -/
def martinBoundary (s : Finset Γ) (μ : Γ → ℝ) (o : Γ) : Set (Γ → ℝ) :=
  martinClosure s μ o \ Set.range (martinEmbedding s μ o)

/-- The defect in the finite-support harmonic equation. -/
def martinDefect (s : Finset Γ) (μ : Γ → ℝ) (z : Γ) (H : Γ → ℝ) : ℝ :=
  H z - ∑ g ∈ s, μ g * H (z * g)

/-- Finite support makes the harmonic defect continuous for pointwise convergence. -/
theorem continuous_martinDefect (s : Finset Γ) (μ : Γ → ℝ) (z : Γ) :
    Continuous (martinDefect s μ z) := by
  unfold martinDefect
  fun_prop

/-- Every actual finite-state column lies in the compactification carrier. -/
theorem martinEmbedding_mem_closure (s : Finset Γ) (μ : Γ → ℝ) (o y : Γ) :
    martinEmbedding s μ o y ∈ martinClosure s μ o :=
  subset_closure ⟨y, rfl⟩

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hgap in
/-- The normalized Green column has a single nonzero harmonic defect, at its pole. -/
theorem martinDefect_embedding (o z y : Γ) :
    martinDefect s μ z (martinEmbedding s μ o y) =
      if z = y then (walkGreen s μ o y)⁻¹ else 0 := by
  unfold martinDefect martinEmbedding martinQuotient
  rw [walkGreen_first_step s μ hgap z y, add_div, Finset.sum_div]
  simp only [mul_div_assoc]
  by_cases hzy : z = y <;> simp [hzy]

include hpos hgen hgap in
/-- The pole is recoverable from its Green column, so the embedding is injective. -/
theorem martinEmbedding_injective (o : Γ) : Function.Injective (martinEmbedding s μ o) := by
  intro x y hxy
  by_contra hne
  have h := congrArg (martinDefect s μ x) hxy
  simp only [martinDefect_embedding s μ hgap, ite_true, hne, ite_false] at h
  exact (inv_ne_zero (walkGreen_ne_zero s μ hpos hgen hgap o x)) h

include hpos hgen hgap in
/-- Positive Harnack intervals bound every point in the closure. -/
theorem martinClosure_coordinate_bounds (o z : Γ) :
    ∃ L U : ℝ, 0 < L ∧ ∀ H ∈ martinClosure s μ o, H z ∈ Icc L U := by
  obtain ⟨L, U, hL, hb⟩ := martinQuotient_bounds s μ hpos hgen hgap o z
  refine ⟨L, U, hL, ?_⟩
  apply closure_minimal
  · rintro H ⟨y, rfl⟩
    exact hb y
  · exact isClosed_Icc.preimage (continuous_apply z)

include hpos hgen hgap in
/-- The closure is compact by its proved coordinate bounds. -/
theorem martinClosure_isCompact (o : Γ) : IsCompact (martinClosure s μ o) := by
  choose L U hL hb using martinQuotient_bounds s μ hpos hgen hgap o
  have hc : IsCompact {H : Γ → ℝ | ∀ z, H z ∈ Icc (L z) (U z)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro H ⟨y, rfl⟩ z
    exact hb z y
  · exact hc.isClosed

include hpos hgen hgap in
/-- Every point of the compactification is normalized at the basepoint. -/
theorem martinClosure_base (o : Γ) {H : Γ → ℝ} (hH : H ∈ martinClosure s μ o) : H o = 1 := by
  have hc : IsClosed {f : Γ → ℝ | f o = 1} := isClosed_eq (continuous_apply o) continuous_const
  apply closure_minimal (t := {f : Γ → ℝ | f o = 1}) ?_ hc hH
  rintro f ⟨y, rfl⟩
  exact martinQuotient_base s μ hpos hgen hgap o y

include hpos hgen hgap in
/-- Every coordinate of every compactification point is strictly positive. -/
theorem martinClosure_pos (o : Γ) {H : Γ → ℝ} (hH : H ∈ martinClosure s μ o) (z : Γ) :
    0 < H z := by
  obtain ⟨L, U, hL, hb⟩ := martinClosure_coordinate_bounds s μ hpos hgen hgap o z
  exact hL.trans_le (hb H hH).1

include hgap in
/-- At a fixed coordinate, a compactification point is either its finite pole or harmonic there. -/
theorem martinClosure_defect_dichotomy (o z : Γ) {H : Γ → ℝ}
    (hH : H ∈ martinClosure s μ o) :
    H = martinEmbedding s μ o z ∨ martinDefect s μ z H = 0 := by
  have hc : IsClosed {f : Γ → ℝ |
      f = martinEmbedding s μ o z ∨ martinDefect s μ z f = 0} :=
    (isClosed_eq continuous_id continuous_const).union
      (isClosed_eq (continuous_martinDefect s μ z) continuous_const)
  apply closure_minimal (t := {f : Γ → ℝ |
    f = martinEmbedding s μ o z ∨ martinDefect s μ z f = 0}) ?_ hc hH
  rintro f ⟨y, rfl⟩
  by_cases hzy : z = y
  · left
    rw [hzy]
  · right
    simp only [martinDefect_embedding s μ hgap, hzy, ite_false]

include hpos hgen hgap in
/-- Within the compactification, precisely the non-finite points are harmonic. -/
theorem martinBoundary_iff_harmonic (o : Γ) (H : Γ → ℝ) :
    H ∈ martinBoundary s μ o ↔
      H ∈ martinClosure s μ o ∧ ∀ z, martinDefect s μ z H = 0 := by
  constructor
  · rintro ⟨hH, hnot⟩
    refine ⟨hH, fun z => ?_⟩
    rcases martinClosure_defect_dichotomy s μ hgap o z hH with he | hz
    · exact (hnot ⟨z, he.symm⟩).elim
    · exact hz
  · rintro ⟨hH, hh⟩
    refine ⟨hH, ?_⟩
    rintro ⟨y, rfl⟩
    have h := hh y
    simp only [martinDefect_embedding s μ hgap, ite_true] at h
    exact (inv_ne_zero (walkGreen_ne_zero s μ hpos hgen hgap o y)) h

include hpos hgen hgap in
/-- The abstract boundary is closed in the pointwise function space. -/
theorem martinBoundary_isClosed (o : Γ) : IsClosed (martinBoundary s μ o) := by
  have he : martinBoundary s μ o = martinClosure s μ o ∩
      ⋂ z : Γ, {H : Γ → ℝ | martinDefect s μ z H = 0} := by
    ext H
    simp only [martinBoundary_iff_harmonic s μ hpos hgen hgap, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [he]
  exact isClosed_closure.inter (isClosed_iInter (fun z =>
    isClosed_eq (continuous_martinDefect s μ z) continuous_const))

include hpos hgen hgap in
/-- The Martin boundary is compact. -/
theorem martinBoundary_isCompact (o : Γ) : IsCompact (martinBoundary s μ o) :=
  (martinClosure_isCompact s μ hpos hgen hgap o).of_isClosed_subset
    (martinBoundary_isClosed s μ hpos hgen hgap o) (fun _ h => h.1)

/-- The boundary kernel is evaluation of an actual point of the Martin boundary. -/
def martinBoundaryKernel (o z : Γ) (ξ : martinBoundary s μ o) : ℝ := ξ.val z

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] in
/-- Evaluation is continuous on the constructed boundary. -/
theorem continuous_martinBoundaryKernel (o z : Γ) : Continuous (martinBoundaryKernel s μ o z) :=
  (continuous_apply z).comp continuous_subtype_val

include hpos hgen hgap in
/-- The constructed boundary kernel is positive. -/
theorem martinBoundaryKernel_pos (o z : Γ) (ξ : martinBoundary s μ o) :
    0 < martinBoundaryKernel s μ o z ξ :=
  martinClosure_pos s μ hpos hgen hgap o ξ.property.1 z

include hpos hgen hgap in
/-- The boundary kernel equals one at the basepoint. -/
theorem martinBoundaryKernel_base (o : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryKernel s μ o o ξ = 1 :=
  martinClosure_base s μ hpos hgen hgap o ξ.property.1

include hpos hgen hgap in
/-- Every constructed boundary kernel solves the forward harmonic equation. -/
theorem martinBoundaryKernel_harmonic (o z : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryKernel s μ o z ξ = ∑ g ∈ s, μ g * martinBoundaryKernel s μ o (z * g) ξ :=
  sub_eq_zero.mp (((martinBoundary_iff_harmonic s μ hpos hgen hgap o ξ.val).mp ξ.property).2 z)

end Singularity
