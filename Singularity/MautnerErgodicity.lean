import Singularity.MautnerDomainAction
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Dynamics.Ergodic.Action.Basic

/-!
# From dilation invariance to ergodicity

For continuous measure-preserving SL(2,ℝ) actions on regular finite measure
spaces, the Mautner argument applies to the actual precomposition action on
Lp. Applying it to indicator functions upgrades invariance under a positive
dilation to invariance under the whole group, modulo null sets.
-/

noncomputable section
open MeasureTheory Filter
open scoped MatrixGroups ENNReal

namespace Singularity

/-- Mautner's theorem applied to the actual continuous domain action on Lp. -/
theorem fixed_Lp_slTwo_of_fixed_dilation {X E : Type*}
    [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
    [MulAction SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X]
    [NormedAddCommGroup E] (μ : Measure X)
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [SMulInvariantMeasure SL(2, ℝ) X μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (τ : ℝ) (hτ : 0 < τ) (f : Lp E p μ)
    (hfix : DomMulAct.mk (dilationMatrix τ) • f = f) (g : SL(2, ℝ)) :
    DomMulAct.mk g • f = f := by
  borelize SL(2, ℝ)
  exact fixed_domain_slTwo_of_fixed_dilation τ hτ f hfix g

/-- Almost-invariant sets for one positive dilation are almost-invariant for every group element. -/
theorem preimage_slTwo_ae_eq_of_dilation {X : Type*}
    [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
    [MulAction SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [SMulInvariantMeasure SL(2, ℝ) X μ]
    (τ : ℝ) (hτ : 0 < τ) {s : Set X} (hs : MeasurableSet s)
    (hinv : (fun x => dilationMatrix τ • x) ⁻¹' s =ᵐ[μ] s) (g : SL(2, ℝ)) :
    (fun x => g • x) ⁻¹' s =ᵐ[μ] s := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let v : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
  have hv : DomMulAct.mk (dilationMatrix τ) • v = v := by
    dsimp [v]
    rw [DomMulAct.mk_smul_indicatorConstLp]
    exact (indicatorConstLp_inj _ _ _ _ (one_ne_zero : (1 : ℝ) ≠ 0)).mpr hinv
  have hg := fixed_Lp_slTwo_of_fixed_dilation μ τ hτ v hv g
  dsimp [v] at hg
  rw [DomMulAct.mk_smul_indicatorConstLp] at hg
  exact (indicatorConstLp_inj _ _ _ _ (one_ne_zero : (1 : ℝ) ≠ 0)).mp hg

/-- Ergodicity of the full group implies ergodicity of each positive diagonal time. -/
theorem ergodic_dilation_of_ergodic_slTwo {X : Type*}
    [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
    [MulAction SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [ErgodicSMul SL(2, ℝ) X μ] (τ : ℝ) (hτ : 0 < τ) :
    Ergodic (fun x : X => dilationMatrix τ • x) μ := by
  refine ⟨measurePreserving_smul (dilationMatrix τ) μ, ⟨?_⟩⟩
  intro s hs hinv
  apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G := SL(2, ℝ)) hs
  intro g
  exact preimage_slTwo_ae_eq_of_dilation μ τ hτ hs (Filter.EventuallyEq.of_eq hinv) g

end Singularity
