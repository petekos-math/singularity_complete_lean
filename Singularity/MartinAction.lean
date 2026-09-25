import Singularity.MartinBoundary

/-!
# The group action on the constructed Martin boundary

Normalized precomposition extends left translation of finite poles. Positivity
of the constructed kernels makes the normalizers nonzero, and the resulting
maps are homeomorphisms of the actual abstract Martin boundary.
-/

noncomputable section
open Set
open scoped Topology

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Normalized precomposition by left multiplication, based at o. -/
def martinTranslate (o g : Γ) (H : Γ → ℝ) : Γ → ℝ :=
  fun z => H (g⁻¹ * z) / H (g⁻¹ * o)

/-- Normalization makes the identity group element act trivially. -/
theorem martinTranslate_one (o : Γ) (H : Γ → ℝ) (ho : H o = 1) :
    martinTranslate o 1 H = H := by
  ext z
  simp [martinTranslate, ho]

/-- The normalized maps obey the left-action multiplication law. -/
theorem martinTranslate_mul (o g h : Γ) (H : Γ → ℝ) (hH : H (h⁻¹ * o) ≠ 0) :
    martinTranslate o g (martinTranslate o h H) = martinTranslate o (g * h) H := by
  ext z
  simp only [martinTranslate, mul_inv_rev, mul_assoc]
  exact div_div_div_cancel_right₀ hH _ _

/-- The harmonic equation transforms equivariantly under normalized precomposition. -/
theorem martinDefect_translate (s : Finset Γ) (μ : Γ → ℝ) (o g z : Γ) (H : Γ → ℝ) :
    martinDefect s μ z (martinTranslate o g H) = martinDefect s μ (g⁻¹ * z) H / H (g⁻¹ * o) := by
  simp only [martinDefect, martinTranslate, sub_div, Finset.sum_div, mul_div_assoc, mul_assoc]

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hgen hgap in
/-- The normalized action extends left translation of actual finite-state columns. -/
theorem martinTranslate_embedding (o g y : Γ) :
    martinTranslate o g (martinEmbedding s μ o y) = martinEmbedding s μ o (g * y) := by
  ext z
  simp only [martinTranslate, martinEmbedding, martinQuotient]
  rw [div_div_div_cancel_right₀ (walkGreen_ne_zero s μ hpos hgen hgap o y)]
  have hz := walkGreen_left s μ g (g⁻¹ * z) y
  have ho := walkGreen_left s μ g (g⁻¹ * o) y
  simp only [mul_inv_cancel_left] at hz ho
  rw [hz, ho]

include hpos hgen hgap in
/-- The action is continuous wherever the proved coordinate lower bounds apply. -/
theorem continuousOn_martinTranslate (o g : Γ) :
    ContinuousOn (martinTranslate o g) (martinClosure s μ o) := by
  apply continuousOn_pi.mpr
  intro z
  exact (continuous_apply (g⁻¹ * z)).continuousOn.div
    (continuous_apply (g⁻¹ * o)).continuousOn
    (fun H hH => ne_of_gt (martinClosure_pos s μ hpos hgen hgap o hH (g⁻¹ * o)))

include hpos hgen hgap in
/-- The action preserves the compactification carrier. -/
theorem martinTranslate_mem_closure (o g : Γ) {H : Γ → ℝ}
    (hH : H ∈ martinClosure s μ o) : martinTranslate o g H ∈ martinClosure s μ o := by
  have hm : MapsTo (martinTranslate o g) (range (martinEmbedding s μ o))
      (range (martinEmbedding s μ o)) := by
    rintro f ⟨y, rfl⟩
    exact ⟨g * y, (martinTranslate_embedding s μ hpos hgen hgap o g y).symm⟩
  exact hm.closure_of_continuousOn (continuousOn_martinTranslate s μ hpos hgen hgap o g) hH

include hpos hgen hgap in
/-- Harmonicity and closure membership show that the abstract boundary is preserved. -/
theorem martinTranslate_mem_boundary (o g : Γ) {H : Γ → ℝ}
    (hH : H ∈ martinBoundary s μ o) : martinTranslate o g H ∈ martinBoundary s μ o := by
  apply (martinBoundary_iff_harmonic s μ hpos hgen hgap o _).mpr
  refine ⟨martinTranslate_mem_closure s μ hpos hgen hgap o g hH.1, ?_⟩
  intro z
  rw [martinDefect_translate,
    ((martinBoundary_iff_harmonic s μ hpos hgen hgap o H).mp hH).2, zero_div]

/-- A group element acts on the actual subtype of Martin-boundary points. -/
def martinBoundaryMap (o g : Γ) (ξ : martinBoundary s μ o) : martinBoundary s μ o :=
  ⟨martinTranslate o g ξ.val, martinTranslate_mem_boundary s μ hpos hgen hgap o g ξ.property⟩

theorem martinBoundaryMap_one (o : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryMap s μ hpos hgen hgap o 1 ξ = ξ := by
  apply Subtype.ext
  exact martinTranslate_one o ξ.val (martinClosure_base s μ hpos hgen hgap o ξ.property.1)

theorem martinBoundaryMap_mul (o g h : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryMap s μ hpos hgen hgap o g (martinBoundaryMap s μ hpos hgen hgap o h ξ) =
      martinBoundaryMap s μ hpos hgen hgap o (g * h) ξ := by
  apply Subtype.ext
  exact martinTranslate_mul o g h ξ.val
    (ne_of_gt (martinClosure_pos s μ hpos hgen hgap o ξ.property.1 (h⁻¹ * o)))

theorem continuous_martinBoundaryMap (o g : Γ) :
    Continuous (martinBoundaryMap s μ hpos hgen hgap o g) := by
  apply Continuous.subtype_mk
  exact ((continuousOn_martinTranslate s μ hpos hgen hgap o g).mono
    (fun _ h => h.1)).domRestrict

/-- Every group element acts by a homeomorphism, with inverse given by its group inverse. -/
def martinBoundaryHomeomorph (o g : Γ) : martinBoundary s μ o ≃ₜ martinBoundary s μ o where
  toFun := martinBoundaryMap s μ hpos hgen hgap o g
  invFun := martinBoundaryMap s μ hpos hgen hgap o g⁻¹
  left_inv ξ := by rw [martinBoundaryMap_mul, inv_mul_cancel, martinBoundaryMap_one]
  right_inv ξ := by rw [martinBoundaryMap_mul, mul_inv_cancel, martinBoundaryMap_one]
  continuous_toFun := continuous_martinBoundaryMap s μ hpos hgen hgap o g
  continuous_invFun := continuous_martinBoundaryMap s μ hpos hgen hgap o g⁻¹

/-- The boundary kernel transformation law, with its explicit positive normalizer. -/
theorem martinBoundaryKernel_translate (o g z : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryKernel s μ o z (martinBoundaryMap s μ hpos hgen hgap o g ξ) =
      martinBoundaryKernel s μ o (g⁻¹ * z) ξ / martinBoundaryKernel s μ o (g⁻¹ * o) ξ := rfl

/-- The verified maps form an actual group action on the abstract boundary. -/
@[instance_reducible]
def martinBoundaryMulAction (o : Γ) : MulAction Γ (martinBoundary s μ o) where
  smul g ξ := martinBoundaryMap s μ hpos hgen hgap o g ξ
  one_smul := martinBoundaryMap_one s μ hpos hgen hgap o
  mul_smul g h ξ := (martinBoundaryMap_mul s μ hpos hgen hgap o g h ξ).symm

/-- The positive normalization factor for the boundary action. -/
def martinBoundaryCocycle (o g : Γ) (ξ : martinBoundary s μ o) : ℝ :=
  martinBoundaryKernel s μ o (g⁻¹ * o) ξ

include hpos hgen hgap in
theorem martinBoundaryCocycle_pos (o g : Γ) (ξ : martinBoundary s μ o) :
    0 < martinBoundaryCocycle s μ o g ξ :=
  martinBoundaryKernel_pos s μ hpos hgen hgap o (g⁻¹ * o) ξ

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] in
theorem continuous_martinBoundaryCocycle (o g : Γ) : Continuous (martinBoundaryCocycle s μ o g) :=
  continuous_martinBoundaryKernel s μ o (g⁻¹ * o)

/-- The exact multiplicative cocycle law for the normalized boundary action. -/
theorem martinBoundaryCocycle_mul (o g h : Γ) (ξ : martinBoundary s μ o) :
    martinBoundaryCocycle s μ o (g * h) ξ =
      martinBoundaryCocycle s μ o g (martinBoundaryMap s μ hpos hgen hgap o h ξ) *
        martinBoundaryCocycle s μ o h ξ := by
  change ξ.val ((g * h)⁻¹ * o) =
    (ξ.val (h⁻¹ * (g⁻¹ * o)) / ξ.val (h⁻¹ * o)) * ξ.val (h⁻¹ * o)
  rw [div_mul_cancel₀ _ (ne_of_gt (martinClosure_pos s μ hpos hgen hgap o ξ.property.1 _))]
  rw [mul_inv_rev, mul_assoc]

end Singularity
