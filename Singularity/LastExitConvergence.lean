import Singularity.FiniteLastExitVertex

/-!
# Last-exit vertices follow the boundary limit of the path

As finite sets exhaust the state space, their last-visit times pass every
fixed time. Thus their selected vertices have the same compactification limit
as the original path. Monotonicity of the finite sets is not required.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Classical
namespace Singularity

/-- Last-visit values for an exhausting family inherit any limit of the path. -/
theorem last_visit_values_tendsto {X B : Type*} [TopologicalSpace B]
    (f v : ℕ → X) (A : ℕ → Set X) (orbit : X → B) (b : B)
    (hexhaust : ∀ x, ∀ᶠ n in atTop, x ∈ A n)
    (hlast : ∀ n, ∃ m, f m = v n ∧ ∀ k, m < k → f k ∉ A n)
    (hlim : Tendsto (fun n => orbit (f n)) atTop (𝓝 b)) :
    Tendsto (fun n => orbit (v n)) atTop (𝓝 b) := by
  apply Filter.tendsto_def.mpr
  intro U hU
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually hU)
  filter_upwards [hexhaust (f N)] with n hn
  obtain ⟨m, hm, ht⟩ := hlast n
  have hNm : N ≤ m := by
    by_contra h
    exact ht N (by omega) hn
  change orbit (v n) ∈ U
  rw [← hm]
  exact hN m hNm

/-- A countable nonempty space admits finite exhaustions containing any fixed
finite set at every stage. -/
theorem exists_finite_exhaustion_containing {X : Type*} [Countable X] [Nonempty X]
    (B : Finset X) :
    ∃ A : ℕ → Finset X, (∀ n, B ⊆ A n) ∧ ∀ x, ∀ᶠ n in atTop, x ∈ A n := by
  obtain ⟨f, hf⟩ := exists_surjective_nat X
  refine ⟨fun n => B ∪ (Finset.range (n + 1)).image f,
    fun n => Finset.subset_union_left, ?_⟩
  intro x
  obtain ⟨k, rfl⟩ := hf x
  apply eventually_atTop.mpr
  refine ⟨k, fun n hn => Finset.mem_union_right _ ?_⟩
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩

variable {Γ : Type*} [Group Γ]

/-- On a transient path, the selected finite-set last-exit vertices have the
same compactification limit as the full path. -/
theorem finiteLastExitVertex_tendsto {B : Type*} [TopologicalSpace B]
    (s : Finset Γ) (A : ℕ → Finset Γ) (x : Γ) (hx : ∀ n, x ∈ A n)
    (hexhaust : ∀ g, ∀ᶠ n in atTop, g ∈ A n) (ω : ℕ → s)
    (hescape : ∀ n, ∀ᶠ k in atTop, walkPosition s x k ω ∉ A n)
    (orbit : Γ → B) (b : B)
    (hlim : Tendsto (fun k => orbit (walkPosition s x k ω)) atTop (𝓝 b)) :
    Tendsto (fun n => orbit (finiteLastExitVertex s (A n) x (hx n) ω)) atTop (𝓝 b) := by
  apply last_visit_values_tendsto (fun k => walkPosition s x k ω)
    (fun n => (finiteLastExitVertex s (A n) x (hx n) ω : Γ))
    (fun n => (A n : Set Γ)) orbit b hexhaust _ hlim
  intro n
  obtain ⟨m, hm, ht⟩ := exists_last_visit_of_eventually_avoid (fun k => walkPosition s x k ω)
    (A n : Set Γ) (hx n) (hescape n)
  have hevent : ω ∈ walkLastExitEver s (A n : Set Γ) x (walkPosition s x m ω) :=
    mem_iUnion.mpr ⟨m, rfl, hm, ht⟩
  have he := congrArg Subtype.val (finiteLastExitVertex_of_mem s (A n) x (hx n) ω
    ⟨walkPosition s x m ω, hm⟩ hevent)
  exact ⟨m, he.symm, ht⟩

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] [Countable Γ]

/-- Almost-sure path convergence transfers to the actual measurable last-exit
vertices under the original infinite random-walk law. -/
theorem finiteLastExitVertex_ae_tendsto {B : Type*} [TopologicalSpace B]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : ℕ → Finset Γ) (x : Γ) (hx : ∀ n, x ∈ A n)
    (hexhaust : ∀ g, ∀ᶠ n in atTop, g ∈ A n) (orbit : Γ → B) (b : (ℕ → s) → B)
    (hlim : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun k => orbit (walkPosition s x k ω)) atTop (𝓝 (b ω))) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => orbit (finiteLastExitVertex s (A n) x (hx n) ω)) atTop (𝓝 (b ω)) := by
  filter_upwards [walkPosition_ae_escape_finite s μ hμ hmass hgap x, hlim] with ω he hl
  exact finiteLastExitVertex_tendsto s A x hx hexhaust ω (fun n => he (A n)) orbit (b ω) hl

end Singularity
