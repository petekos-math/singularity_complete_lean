import Singularity.CompactFundamentalDomain

/-!
# A common compactly supported transversal and quotient measures

Choose one geometric transversal, independent of the measure. It is a
fundamental domain for every measure. Locally finite measures therefore give
finite quotient measures; right lattice invariance makes the quotient
independent of the fundamental domain and preserves any left translation
which preserves the original measure.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Topology
open scoped Pointwise

namespace Singularity

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]

/-- A geometric measurable transversal with a compact bound, independent of any measure. -/
theorem exists_compact_coset_transversal :
    ∃ S K : Set G, MeasurableSet S ∧ IsCompact K ∧ S ⊆ K ∧
      Set.InjOn (QuotientGroup.mk : G → G ⧸ Γ) S ∧
      (QuotientGroup.mk : G → G ⧸ Γ) '' S = univ := by
  have hc := (Γ.isQuotientCoveringMap ⟨inferInstance⟩).isCoveringMap.isLocalHomeomorph
  exact exists_compact_measurable_transversal (QuotientGroup.mk : G → G ⧸ Γ)
    hc QuotientGroup.mk_surjective

/-- The common transversal used for all measures on this coset quotient. -/
def compactCosetTransversal : Set G := (exists_compact_coset_transversal Γ).choose

/-- A compact set containing the chosen transversal. -/
def compactCosetTransversalBound : Set G := (exists_compact_coset_transversal Γ).choose_spec.choose

theorem compactCosetTransversal_measurable : MeasurableSet (compactCosetTransversal Γ) :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.1

theorem compactCosetTransversalBound_compact : IsCompact (compactCosetTransversalBound Γ) :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.2.1

theorem compactCosetTransversal_subset : compactCosetTransversal Γ ⊆ compactCosetTransversalBound Γ :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.2.2.1

theorem compactCosetTransversal_injective :
    Set.InjOn (QuotientGroup.mk : G → G ⧸ Γ) (compactCosetTransversal Γ) :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.2.2.2.1

theorem compactCosetTransversal_surjective :
    (QuotientGroup.mk : G → G ⧸ Γ) '' compactCosetTransversal Γ = univ :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.2.2.2.2

/-- The same geometric transversal is a fundamental domain for every measure. -/
theorem compactCosetTransversal_fundamental (m : Measure G) :
    IsFundamentalDomain Γ.op (compactCosetTransversal Γ) m :=
  isFundamentalDomain_of_quotient_transversal Γ m (compactCosetTransversal_measurable Γ)
    (compactCosetTransversal_injective Γ) (compactCosetTransversal_surjective Γ)

/-- Push the measure on the common transversal to the quotient. -/
def compactCosetQuotientMeasure (m : Measure G) : Measure (G ⧸ Γ) :=
  (m.restrict (compactCosetTransversal Γ)).map QuotientGroup.mk

theorem compactCosetTransversal_finite (m : Measure G) [IsLocallyFiniteMeasure m] :
    m (compactCosetTransversal Γ) < ⊤ :=
  (measure_mono (compactCosetTransversal_subset Γ)).trans_lt
    (compactCosetTransversalBound_compact Γ).measure_lt_top

theorem compactCosetQuotientMeasure_finite (m : Measure G) [IsLocallyFiniteMeasure m] :
    IsFiniteMeasure (compactCosetQuotientMeasure Γ m) := by
  let : Fact (m (compactCosetTransversal Γ) < ⊤) := ⟨compactCosetTransversal_finite Γ m⟩
  unfold compactCosetQuotientMeasure
  infer_instance

theorem compactCosetQuotientMeasure_univ (m : Measure G) :
    compactCosetQuotientMeasure Γ m univ = m (compactCosetTransversal Γ) := by
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  rw [compactCosetQuotientMeasure, Measure.map_apply hπ MeasurableSet.univ]
  simp

/-- A nonzero right lattice invariant measure descends to a nonzero quotient measure. -/
theorem compactCosetQuotientMeasure_ne_zero (m : Measure G) [SMulInvariantMeasure Γ.op G m]
    (hm : m ≠ 0) : compactCosetQuotientMeasure Γ m ≠ 0 := by
  let : Countable Γ := countable_of_Lindelof_of_discrete
  have hpos := (compactCosetTransversal_fundamental Γ m).measure_ne_zero hm
  intro he
  apply hpos
  rw [← compactCosetQuotientMeasure_univ Γ m, he]
  rfl

/-- The quotient is invariant under any single left translation preserving the upstairs measure. -/
theorem compactCosetQuotientMeasure_left_invariant (m : Measure G)
    [SMulInvariantMeasure Γ.op G m] (a : G)
    (ha : MeasurePreserving (fun x : G => a * x) m m) :
    MeasurePreserving (fun q : G ⧸ Γ => a • q)
      (compactCosetQuotientMeasure Γ m) (compactCosetQuotientMeasure Γ m) := by
  let : Countable Γ := countable_of_Lindelof_of_discrete
  let S := compactCosetTransversal Γ
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have hπ : Measurable π := measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  have hS := compactCosetTransversal_fundamental Γ m
  have hS' : IsFundamentalDomain Γ.op ((fun x : G => a * x) ⁻¹' S) m := by
    apply hS.preimage_of_equiv ha.quasiMeasurePreserving Function.bijective_id
    intro γ x
    change a * (x * MulOpposite.unop (γ : Gᵐᵒᵖ)) = (a * x) * MulOpposite.unop (γ : Gᵐᵒᵖ)
    exact (mul_assoc _ _ _).symm
  have he : compactCosetQuotientMeasure Γ m = (m.restrict ((fun x : G => a * x) ⁻¹' S)).map π :=
    hS.quotientMeasure_eq m hS'
  refine ⟨measurable_const_smul a, ?_⟩
  conv_lhs => rw [he]
  rw [Measure.map_map (measurable_const_smul a) hπ]
  have hcomm : (fun q : G ⧸ Γ => a • q) ∘ π = π ∘ (fun x : G => a * x) := rfl
  rw [hcomm, ← Measure.map_map hπ ha.measurable,
    (ha.restrict_preimage (compactCosetTransversal_measurable Γ)).map_eq]
  rfl

/-- Absolute continuity upstairs passes to the common quotient construction. -/
theorem compactCosetQuotientMeasure_absolutelyContinuous (m ρ : Measure G) (h : m ≪ ρ) :
    compactCosetQuotientMeasure Γ m ≪ compactCosetQuotientMeasure Γ ρ :=
  (h.restrict (compactCosetTransversal Γ)).map
    (show Measurable (QuotientGroup.mk : G → G ⧸ Γ) from measurable_quotient_mk' (s := QuotientGroup.leftRel Γ))

/-- Null quotient sets are exactly those whose full frame preimages are null. -/
theorem compactCosetQuotientMeasure_null_iff (m : Measure G)
    [SMulInvariantMeasure Γ.op G m] {A : Set (G ⧸ Γ)} (hA : MeasurableSet A) :
    compactCosetQuotientMeasure Γ m A = 0 ↔ m (QuotientGroup.mk ⁻¹' A) = 0 := by
  let : Countable Γ := countable_of_Lindelof_of_discrete
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ Γ) :=
    measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  rw [compactCosetQuotientMeasure, Measure.map_apply hπ hA, Measure.restrict_apply (hπ hA)]
  constructor
  · intro h
    apply (compactCosetTransversal_fundamental Γ m).measure_zero_of_invariant _ _ h
    intro γ
    ext x
    simp only [mem_smul_set_iff_inv_smul_mem, mem_preimage]
    have he : (QuotientGroup.mk (γ⁻¹ • x) : G ⧸ Γ) = QuotientGroup.mk x :=
      @Quotient.sound G (MulAction.orbitRel Γ.op G) _ _ ⟨γ⁻¹, rfl⟩
    exact he ▸ Iff.rfl
  · exact fun h => measure_mono_null inter_subset_left h

/-- For right lattice invariant measures, quotient absolute continuity is equivalent
 to absolute continuity upstairs. -/
theorem compactCosetQuotientMeasure_absolutelyContinuous_iff (m ρ : Measure G)
    [SMulInvariantMeasure Γ.op G m] [SMulInvariantMeasure Γ.op G ρ] :
    compactCosetQuotientMeasure Γ m ≪ compactCosetQuotientMeasure Γ ρ ↔ m ≪ ρ := by
  let : Countable Γ := countable_of_Lindelof_of_discrete
  constructor
  · intro h
    apply AbsolutelyContinuous.mk
    intro A hA hρ
    have he : (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' ((QuotientGroup.mk : G → G ⧸ Γ) '' A) =
        ⋃ γ : Γ.op, (fun x : G => γ • x) '' A :=
      MulAction.quotient_preimage_image_eq_union_mul A (G := Γ.op)
    have himage : MeasurableSet ((QuotientGroup.mk : G → G ⧸ Γ) '' A) := by
      apply measurableSet_quotient.mpr
      change MeasurableSet ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' ((QuotientGroup.mk : G → G ⧸ Γ) '' A))
      rw [he]
      exact MeasurableSet.iUnion fun γ => hA.const_smul γ
    have hpre : ρ ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' ((QuotientGroup.mk : G → G ⧸ Γ) '' A)) = 0 := by
      rw [he]
      apply measure_iUnion_null
      intro γ
      change ρ (γ • A) = 0
      rw [measure_smul, hρ]
    have hq := h ((compactCosetQuotientMeasure_null_iff Γ ρ himage).mpr hpre)
    exact measure_mono_null (Set.subset_preimage_image _ _)
      ((compactCosetQuotientMeasure_null_iff Γ m himage).mp hq)
  · exact compactCosetQuotientMeasure_absolutelyContinuous Γ m ρ

end Singularity
