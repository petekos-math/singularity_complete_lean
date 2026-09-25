import Singularity.WalkBoundaryLimit

/-!
# Independence at an arbitrary deterministic time

The whole finite prefix is independent of the whole shifted future. In
particular the current position is independent of the future increments.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace Singularity

variable {Γ : Type*} [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- The finite prefix and all increments after it are independent. -/
theorem infiniteWalkLaw_prefix_tail_independent (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) :
    IndepFun (walkPrefix s n) (fun ω k => ω (k + n)) (infiniteWalkLaw s μ hμ hmass) := by
  apply IndepFun.indepFun_process (measurable_walkPrefix s n) (fun _ => by fun_prop)
  intro I
  have hdis : Disjoint (Finset.range n) (I.image (fun k => k + n)) := by
    apply Finset.disjoint_left.mpr
    intro k hk hj
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_range.mp hk
    omega
  have hi := (infiniteWalkLaw_independent s μ hμ hmass).indepFun_finset
    (Finset.range n) (I.image (fun k => k + n)) hdis (fun _ => by fun_prop)
  exact hi.comp
    (measurable_of_countable (fun v : (Finset.range n) → s =>
      (walkWordEquivFin s n).symm (fun i => v ⟨i.val, Finset.mem_range.mpr i.isLt⟩)))
    (measurable_pi_lambda _ (fun i : I => measurable_pi_apply
      ⟨i.val + n, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩))

/-- The position at time n is independent of all increments after time n. -/
theorem infiniteWalkLaw_position_tail_independent [Group Γ] (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (x : Γ) (n : ℕ) :
    IndepFun (walkPosition s x n) (fun ω k => ω (k + n)) (infiniteWalkLaw s μ hμ hmass) :=
  (infiniteWalkLaw_prefix_tail_independent s μ hμ hmass n).comp
    (measurable_of_countable (walkEndpoint s n x)) measurable_id

end Singularity
