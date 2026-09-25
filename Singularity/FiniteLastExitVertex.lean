import Singularity.FiniteLastExitLaw

/-!
# The measurable last-exit vertex on the actual path space

On the full-measure event of a last exit, the selected vertex is its unique
location. The fallback is the starting vertex. Its pushforward law is exactly
the last-exit PMF already identified by the Green formula.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The last-exit vertex, with the starting point as fallback off the event
where a last exit exists. -/
def finiteLastExitVertex (s A : Finset Γ) (x : Γ) (hx : x ∈ A) (ω : ℕ → s) : A :=
  if h : ∃ a : A, ω ∈ walkLastExitEver s (A : Set Γ) x a then h.choose else ⟨x, hx⟩

/-- The selected vertex is the unique vertex specified by any last-exit event. -/
theorem finiteLastExitVertex_of_mem (s A : Finset Γ) (x : Γ) (hx : x ∈ A)
    (ω : ℕ → s) (a : A) (ha : ω ∈ walkLastExitEver s (A : Set Γ) x a) :
    finiteLastExitVertex s A x hx ω = a := by
  have h : ∃ b : A, ω ∈ walkLastExitEver s (A : Set Γ) x b := ⟨a, ha⟩
  rw [finiteLastExitVertex, dite_eq_left h]
  by_contra he
  exact Set.disjoint_left.mp (walkLastExitEver_disjoint s (A : Set Γ) x
    (fun hh => he (Subtype.ext hh))) h.choose_spec ha

/-- On the union of last-exit events, the chosen vertex satisfies its event. -/
theorem finiteLastExitVertex_mem (s A : Finset Γ) (x : Γ) (hx : x ∈ A) (ω : ℕ → s)
    (h : ∃ a : A, ω ∈ walkLastExitEver s (A : Set Γ) x a) :
    ω ∈ walkLastExitEver s (A : Set Γ) x (finiteLastExitVertex s A x hx ω) := by
  rw [finiteLastExitVertex, dite_eq_left h]
  exact h.choose_spec

/-- The only extra part of a fiber is the fallback event, when the requested
vertex is the chosen starting point. -/
theorem finiteLastExitVertex_fiber (s A : Finset Γ) (x : Γ) (hx : x ∈ A) (a : A) :
    {ω | finiteLastExitVertex s A x hx ω = a} = walkLastExitEver s (A : Set Γ) x a ∪
      (if a = ⟨x, hx⟩ then (⋃ b : A, walkLastExitEver s (A : Set Γ) x b)ᶜ else ∅) := by
  ext ω
  by_cases h : ∃ b : A, ω ∈ walkLastExitEver s (A : Set Γ) x b
  · have hmem : ω ∈ ⋃ b : A, walkLastExitEver s (A : Set Γ) x b := mem_iUnion.mpr h
    have hiff : finiteLastExitVertex s A x hx ω = a ↔ ω ∈ walkLastExitEver s (A : Set Γ) x a := by
      constructor
      · intro he
        exact he ▸ finiteLastExitVertex_mem s A x hx ω h
      · exact finiteLastExitVertex_of_mem s A x hx ω a
    by_cases ha : a = ⟨x, hx⟩
    · simpa only [mem_ofPred_eq, mem_union, ite_eq_left ha, mem_compl_iff, hmem,
        not_true_eq_false, or_false] using hiff
    · simpa only [mem_ofPred_eq, mem_union, ite_eq_right ha, mem_empty_iff_false, or_false] using hiff
  · have hmem : ω ∉ ⋃ b : A, walkLastExitEver s (A : Set Γ) x b := by simpa using h
    have ha : ω ∉ walkLastExitEver s (A : Set Γ) x a := fun hh => h ⟨a, hh⟩
    have he : finiteLastExitVertex s A x hx ω = ⟨x, hx⟩ := by
      rw [finiteLastExitVertex, dite_eq_right h]
    by_cases hb : a = ⟨x, hx⟩
    · simp only [mem_ofPred_eq, mem_union, ite_eq_left hb, mem_compl_iff, hmem,
        not_false_eq_true, or_true, iff_true]
      exact he.trans hb.symm
    · simp only [mem_ofPred_eq, he, mem_union, ite_eq_right hb, mem_empty_iff_false,
        or_false, ha, iff_false]
      exact Ne.symm hb

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- The actual last-exit vertex is a measurable random variable. -/
theorem measurable_finiteLastExitVertex (s A : Finset Γ) (x : Γ) (hx : x ∈ A) :
    Measurable (finiteLastExitVertex s A x hx) := by
  apply measurable_to_countable'
  intro a
  change MeasurableSet {ω | finiteLastExitVertex s A x hx ω = a}
  rw [finiteLastExitVertex_fiber]
  apply (measurableSet_walkLastExitEver s (A : Set Γ) A.measurableSet x a).union
  split_ifs
  · exact (MeasurableSet.iUnion (fun b : A =>
      measurableSet_walkLastExitEver s (A : Set Γ) A.measurableSet x b)).compl
  · exact MeasurableSet.empty

variable [MeasurableMul Γ] [Countable Γ]

/-- The selected last-exit vertex realizes the PMF on the infinite walk space. -/
theorem finiteLastExitVertex_law (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Finset Γ) (x : Γ) (hx : x ∈ A) :
    Measure.map (finiteLastExitVertex s A x hx) (infiniteWalkLaw s μ hμ hmass) =
      (finiteLastExitLaw s μ hμ hmass hgap A x hx).toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_finiteLastExitVertex s A x hx) (measurableSet_singleton a),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  change infiniteWalkLaw s μ hμ hmass {ω | finiteLastExitVertex s A x hx ω = a} =
    infiniteWalkLaw s μ hμ hmass (walkLastExitEver s (A : Set Γ) x a)
  apply measure_congr
  filter_upwards [walkLastExitEver_ae_cover s μ hμ hmass hgap A x hx] with ω hω
  have h := finiteLastExitVertex_mem s A x hx ω (mem_iUnion.mp hω)
  apply propext
  constructor
  · intro he
    exact he ▸ h
  · exact finiteLastExitVertex_of_mem s A x hx ω a

end Singularity
