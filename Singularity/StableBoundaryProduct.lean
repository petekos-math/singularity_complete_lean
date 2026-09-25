import Singularity.BoundaryPairInvariance
import Singularity.StableCesaro

/-!
# One-sided transfer on the off-diagonal boundary product

The diagonal prevents using a literal full product chart. This file keeps
that exceptional set explicit. A property saturated when only the backward
endpoint changes transfers to an arbitrary backward marginal and an
absolutely continuous forward marginal. The forward measures are nonatomic.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter OnePoint

namespace Singularity

/-- Product saturation may exclude equality of the two boundary coordinates. -/
theorem ae_product_of_fibre_saturation_off_diagonal {X H : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace H]
    (α α' β β' : Measure X) (η : Measure H)
    [NeZero α] [SFinite β] [SFinite β'] [SFinite η] [NullSingletonClass β']
    (hβ : β' ≪ β) (P : X × (X × H) → Prop) (hP : MeasurableSet {p | P p})
    (hdiag : ∀ x h, P (x, (x, h)))
    (hsat : ∀ a a' b h, a ≠ b → a' ≠ b → P (a, (b, h)) → P (a', (b, h)))
    (h : ∀ᵐ p ∂α.prod (β.prod η), P p) : ∀ᵐ p ∂α'.prod (β'.prod η), P p := by
  obtain ⟨a, ha⟩ := (ae_ae_of_ae_prod h).exists
  have ha' : ∀ᵐ b ∂β'.prod η, P (a, b) := (hβ.prod AbsolutelyContinuous.rfl).ae_le ha
  have hne : ∀ᵐ b ∂β'.prod η, a ≠ b.1 := by
    apply Measure.quasiMeasurePreserving_fst.ae
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton'] using measure_singleton a (μ := β')
  apply (ae_prod_iff_ae_ae hP).mpr
  exact Eventually.of_forall fun a' => (ha'.and hne).mono fun b hb => by
    by_cases heq : a' = b.1
    · subst a'
      exact hdiag _ _
    · exact hsat a a' b.1 b.2 hb.2 heq hb.1

/-- Put boundary-pair/fibre coordinates into backward × (forward × fibre) order. -/
def boundaryPairFiberEmbedding {H : Type*} (q : BoundaryPair × H) :
    OnePoint ℝ × (OnePoint ℝ × H) := (q.1.val.1, (q.1.val.2, q.2))

theorem measurableEmbedding_boundaryPairFiber {H : Type*} [MeasurableSpace H] :
    MeasurableEmbedding (boundaryPairFiberEmbedding (H := H)) :=
  MeasurableEquiv.prodAssoc.measurableEmbedding.comp
    (measurableEmbedding_boundaryPair.prodMap MeasurableEmbedding.id)

/-- Nonatomicity of the forward marginal makes the omitted diagonal null. -/
theorem boundaryPairFiberEmbedding_map {H : Type*} [MeasurableSpace H]
    (α β : Measure (OnePoint ℝ)) (η : Measure H)
    [IsFiniteMeasure α] [IsFiniteMeasure β] [SFinite η]
    [NullSingletonClass β] :
    ((boundaryPairMeasure α β).prod η).map boundaryPairFiberEmbedding = α.prod (β.prod η) := by
  change (((boundaryPairMeasure α β).prod η).map
    (MeasurableEquiv.prodAssoc ∘ Prod.map Subtype.val id)) = _
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.measurable
    (measurable_subtype_coe.prodMap measurable_id), ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
    boundaryPairMeasure_map_eq, Measure.map_id, Measure.prodAssoc_prod]

/-- Saturated measurable properties transfer under one-sided absolute continuity. -/
theorem ae_boundaryPair_product_of_fibre_saturation {H : Type*} [MeasurableSpace H]
    (α α' β β' : Measure (OnePoint ℝ)) (η : Measure H)
    [NeZero α] [IsFiniteMeasure α] [IsFiniteMeasure α']
    [IsFiniteMeasure β] [IsFiniteMeasure β'] [SFinite η]
    [NullSingletonClass β] [NullSingletonClass β']
    (hβ : β' ≪ β) (P : BoundaryPair × H → Prop) (hP : MeasurableSet {q | P q})
    (hsat : ∀ p q h, p.val.2 = q.val.2 → P (p, h) → P (q, h))
    (h : ∀ᵐ q ∂(boundaryPairMeasure α β).prod η, P q) :
    ∀ᵐ q ∂(boundaryPairMeasure α' β').prod η, P q := by
  let E : BoundaryPair × H → OnePoint ℝ × (OnePoint ℝ × H) := boundaryPairFiberEmbedding
  have hE : MeasurableEmbedding E := measurableEmbedding_boundaryPairFiber
  let Q : OnePoint ℝ × (OnePoint ℝ × H) → Prop := fun q => q ∉ E '' {p | ¬P p}
  have hQ : MeasurableSet {q | Q q} := (hE.measurableSet_image.mpr hP.compl).compl
  have hQE (q : BoundaryPair × H) : Q (E q) ↔ P q := by
    simp only [Q, hE.injective.mem_set_image, Set.mem_ofPred_eq, not_not]
  have hQref : ∀ᵐ q ∂α.prod (β.prod η), Q q := by
    rw [← boundaryPairFiberEmbedding_map α β η]
    exact (hE.ae_map_iff).mpr (h.mono fun q hq => (hQE q).mpr hq)
  have hQtgt : ∀ᵐ q ∂α'.prod (β'.prod η), Q q := by
    apply ae_product_of_fibre_saturation_off_diagonal α α' β β' η hβ Q hQ
    · intro x h₀
      rintro ⟨⟨p, h₁⟩, _, he⟩
      have hfst := congrArg Prod.fst he
      have hsnd := congrArg (fun q : OnePoint ℝ × (OnePoint ℝ × H) => q.2.1) he
      exact p.property (hfst.trans hsnd.symm)
    · intro a a' b h₀ hab hab' hq
      have he : E (⟨(a, b), hab⟩, h₀) = (a, (b, h₀)) := rfl
      have he' : E (⟨(a', b), hab'⟩, h₀) = (a', (b, h₀)) := rfl
      rw [← he, hQE] at hq
      rw [← he', hQE]
      exact hsat ⟨(a, b), hab⟩ ⟨(a', b), hab'⟩ h₀ rfl hq
    · exact hQref
  rw [← boundaryPairFiberEmbedding_map α' β' η] at hQtgt
  exact ((hE.ae_map_iff).mp hQtgt).mono fun q hq => (hQE q).mp hq

end Singularity
