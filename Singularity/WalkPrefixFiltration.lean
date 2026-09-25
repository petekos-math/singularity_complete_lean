import Singularity.WalkPrefixTail
import Mathlib.Probability.Martingale.Convergence

/-!
# The increasing finite-prefix filtration of the actual path space

The first n coordinates generate a filtration whose supremum is the whole
product sigma-algebra. Conditional expectations therefore recover every
integrable measurable real path observable almost surely.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
namespace Singularity

/-- Information carried by the first n coordinates of an infinite path. -/
def walkPrefixFiltration (S : Type*) [MeasurableSpace S] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) where
  seq n := ⨆ i : Fin n, MeasurableSpace.comap (fun ω : ℕ → S => ω i.val) inferInstance
  mono' := by
    intro n m hnm
    refine iSup_le fun i => ?_
    exact le_iSup_of_le (⟨i.val, lt_of_lt_of_le i.isLt hnm⟩ : Fin m) le_rfl
  le' n := iSup_le fun i => (measurable_pi_apply i.val).comap_le

/-- The prefix sigma-algebra is the pullback by its finite coordinate tuple. -/
theorem walkPrefixFiltration_eq_comap (S : Type*) [MeasurableSpace S] (n : ℕ) :
    walkPrefixFiltration S n = MeasurableSpace.comap
      (fun (ω : ℕ → S) (i : Fin n) => ω i.val) inferInstance := by
  exact (MeasurableSpace.comap_process_pi (fun (i : Fin n) (ω : ℕ → S) => ω i.val)).symm

/-- Every measurable path event is measurable with respect to the supremum
of the finite-prefix sigma-algebras. -/
theorem walkPrefixFiltration_iSup (S : Type*) [MeasurableSpace S] :
    (⨆ n, walkPrefixFiltration S n) = (inferInstance : MeasurableSpace (ℕ → S)) := by
  apply le_antisymm (iSup_le (walkPrefixFiltration S).le)
  change (⨆ k : ℕ, MeasurableSpace.comap (fun ω : ℕ → S => ω k) inferInstance) ≤ _
  refine iSup_le fun k => le_iSup_of_le (k + 1) ?_
  exact le_iSup_of_le (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) le_rfl

/-- Levy's upward convergence theorem for the actual infinite walk law. -/
theorem infiniteWalkLaw_condExp_prefix_tendsto
    {Γ : Type*} [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (f : (ℕ → s) → ℝ)
    (hf : Measurable f) (hint : Integrable f (infiniteWalkLaw s μ hμ hmass)) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Tendsto (fun n => (infiniteWalkLaw s μ hμ hmass)[f | walkPrefixFiltration s n] ω)
        atTop (𝓝 (f ω)) := by
  apply hint.tendsto_ae_condExp
  rw [walkPrefixFiltration_iSup]
  exact hf.stronglyMeasurable

end Singularity
