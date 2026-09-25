import Singularity.BoundaryFirstEntrance
import Singularity.FiniteTranslateDensity

/-!
# Entrance representation when a boundary event forces a finite visit

If paths ending in a measurable boundary region almost surely hit A, the
translated hitting law restricted to that region is the finite mixture of
the laws from its first entrance vertices. The stopping formula is derived
from deterministic-time independence and disjoint entrance events.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal
namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ] [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
  (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (b : (ℕ → s) → B) (hb : Measurable b)
  (hstep : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
    b ω = (ω 0 : Γ) • b (fun k => ω (k + 1)))

include hb hstep hgap

/-- A boundary event forcing a visit to A has the exact finite entrance sum. -/
theorem walkBoundaryLaw_finite_entrance (A : Finset Γ) (x : Γ)
    {E : Set B} (hE : MeasurableSet E)
    (hvisit : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      x • b ω ∈ E → ∃ n, walkPosition s x n ω ∈ A) :
    walkBoundaryLaw s μ hμ hmass b ((fun ξ : B => x • ξ) ⁻¹' E) =
      ∑ a : A, ENNReal.ofReal (firstEntranceKernel s μ (A : Set Γ) x a) *
        walkBoundaryLaw s μ hμ hmass b ((fun ξ : B => (a : Γ) • ξ) ⁻¹' E) := by
  let P := infiniteWalkLaw s μ hμ hmass
  let V : Set (ℕ → s) := {ω | x • b ω ∈ E}
  have he : V =ᵐ[P] ⋃ a : A, walkFirstEntranceEver s (A : Set Γ) x a ∩ V := by
    filter_upwards [hvisit] with ω hω
    apply propext
    constructor
    · intro hv
      have hh : ω ∈ ⋃ a : Γ, walkFirstEntranceEver s (A : Set Γ) x a := by
        rw [← walk_hit_eq_union_firstEntrance]
        exact hω hv
      obtain ⟨a, ha⟩ := mem_iUnion.mp hh
      obtain ⟨n, hn⟩ := mem_iUnion.mp ha
      have haA := ((mem_walkFirstEntranceEvent s (A : Set Γ) x a n ω).mp hn).2.2
      exact mem_iUnion.mpr ⟨⟨a, haA⟩, mem_iUnion.mpr ⟨n, hn⟩, hv⟩
    · intro hv
      obtain ⟨a, ha⟩ := mem_iUnion.mp hv
      exact ha.2
  have hm (a : A) : MeasurableSet (walkFirstEntranceEver s (A : Set Γ) x a ∩ V) :=
    (measurableSet_walkFirstEntranceEver s (A : Set Γ) x a).inter
      (hE.preimage ((measurable_const_smul x).comp hb))
  have hd : Pairwise (fun a c : A => Disjoint
      (walkFirstEntranceEver s (A : Set Γ) x a ∩ V)
      (walkFirstEntranceEver s (A : Set Γ) x c ∩ V)) := by
    intro a c hac
    exact (walkFirstEntranceEver_disjoint s (A : Set Γ) x
      (fun he => hac (Subtype.ext he))).mono inter_subset_left inter_subset_left
  rw [walkBoundaryLaw, Measure.map_apply hb (hE.preimage (measurable_const_smul x))]
  change P V = _
  rw [measure_congr he, measure_iUnion hd hm, tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  exact walkFirstEntranceEver_boundary_probability s μ hμ hmass b hb hstep hgap
    (A : Set Γ) x a hE

/-- Equality of restricted translated hitting laws, from the geometric
condition that the indicated boundary event forces entrance into A. -/
theorem walkBoundaryLaw_restrict_eq_finite_entrance (A : Finset Γ) (x : Γ)
    {E : Set B} (hE : MeasurableSet E)
    (hvisit : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      x • b ω ∈ E → ∃ n, walkPosition s x n ω ∈ A) :
    (Measure.map (fun ξ : B => x • ξ) (walkBoundaryLaw s μ hμ hmass b)).restrict E =
      ∑ a : A, ENNReal.ofReal (firstEntranceKernel s μ (A : Set Γ) x a) •
        (Measure.map (fun ξ : B => (a : Γ) • ξ) (walkBoundaryLaw s μ hμ hmass b)).restrict E := by
  ext S hS
  simp only [Measure.restrict_apply hS, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_const_smul _) (hS.inter hE)]
  apply walkBoundaryLaw_finite_entrance s μ hμ hmass hgap b hb hstep A x (hS.inter hE)
  filter_upwards [hvisit] with ω hω hmem
  exact hω hmem.2

/-- The actual translated densities satisfy the entrance representation on
any boundary region whose paths almost surely visit the finite entrance set. -/
theorem walkBoundaryLaw_density_finite_entrance
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) (walkBoundaryLaw s μ hμ hmass b) ≪
      walkBoundaryLaw s μ hμ hmass b)
    (A : Finset Γ) (x : Γ) {E : Set B} (hE : MeasurableSet E)
    (hvisit : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      x • b ω ∈ E → ∃ n, walkPosition s x n ω ∈ A) :
    ∀ᵐ ξ ∂walkBoundaryLaw s μ hμ hmass b, ξ ∈ E →
      stationaryRealDensity (walkBoundaryLaw s μ hμ hmass b) x ξ =
        ∑ a : A, firstEntranceKernel s μ (A : Set Γ) x a *
          stationaryRealDensity (walkBoundaryLaw s μ hμ hmass b) (a : Γ) ξ := by
  let := walkBoundaryLaw_probability s μ hμ hmass b hb
  exact stationaryRealDensity_finite_mixture_on_set _ hq A
    (fun a => firstEntranceKernel s μ (A : Set Γ) x a)
    (fun a => firstEntranceKernel_nonneg s μ hμ (A : Set Γ) x a) x hE
    (walkBoundaryLaw_restrict_eq_finite_entrance s μ hμ hmass hgap b hb hstep A x hE hvisit)

end Singularity
