import Singularity.Operators
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.NormNum

/-!
# Strong ℓ² convergence from a square-summable envelope

This is the analytic limit argument needed for the normalized Green rows and
columns. The geometric construction of their envelope remains separate.
-/

noncomputable section
open Filter
open scoped Topology

namespace Singularity

abbrev SequenceL2 (ι : Type*) := lp (fun _ : ι => ℂ) 2

/-- Square-sum formula for the sequence-space norm. -/
theorem sequenceL2_norm_sq {ι : Type*} (f : SequenceL2 ι) :
    ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f

/-- An envelope with summable square puts the bounded function in ℓ². -/
theorem mem_sequenceL2_of_bound {ι : Type*} {f : ι → ℂ} {b : ι → ℝ}
    (hb : Summable (fun i => b i ^ 2)) (hbound : ∀ i, ‖f i‖ ≤ b i) :
    Memℓp f 2 := by
  apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
  have hs : Summable (fun i => ‖f i‖ ^ 2) := by
    apply hb.of_nonneg_of_le (fun i => sq_nonneg _)
    intro i
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound i) 2
  simpa using hs

/-- Pointwise convergence and one square-summable envelope imply norm
convergence. No countability assumption on the coordinate set is needed. -/
theorem sequenceL2_tendsto_of_dominated {ι α : Type*} {l : Filter α} [l.NeBot]
    {u : α → SequenceL2 ι} {v : SequenceL2 ι} {b : ι → ℝ}
    (hb : Summable (fun i => b i ^ 2))
    (hbound : ∀ᶠ n in l, ∀ i, ‖u n i‖ ≤ b i)
    (hpoint : ∀ i, Tendsto (fun n => u n i) l (𝓝 (v i))) :
    Tendsto u l (𝓝 v) := by
  have hvbound : ∀ i, ‖v i‖ ≤ b i := fun i =>
    le_of_tendsto (hpoint i).norm (hbound.mono (fun n hn => hn i))
  have hs : Tendsto (fun n => ∑' i, ‖u n i - v i‖ ^ 2) l (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence
      (𝓕 := l) (f := fun n i => ‖u n i - v i‖ ^ 2)
      (bound := fun i => 4 * b i ^ 2) (g := fun _ : ι => (0 : ℝ))
      (hb.mul_left 4) ?_ ?_
    · simpa only [tsum_zero] using h
    · intro i
      simpa using (((hpoint i).sub_const (v i)).norm.pow 2)
    · filter_upwards [hbound] with n hn i
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have htri := norm_sub_le (u n i) (v i)
      have hbi : 0 ≤ b i := (norm_nonneg _).trans (hn i)
      have hni := hn i
      have hvi := hvbound i
      have hsquare := pow_le_pow_left₀ (norm_nonneg (u n i - v i))
        (htri.trans (add_le_add hni hvi)) 2
      nlinarith
  have hsq : Tendsto (fun n => ‖u n - v‖ ^ 2) l (𝓝 0) := by
    simpa only [sequenceL2_norm_sq, lp.coeFn_sub, Pi.sub_apply] using hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot

/-- The raw coordinate limit itself belongs to ℓ² and is the strong limit. -/
theorem sequenceL2_limit_exists {ι α : Type*} {l : Filter α} [l.NeBot]
    {u : α → SequenceL2 ι} {v : ι → ℂ} {b : ι → ℝ}
    (hb : Summable (fun i => b i ^ 2))
    (hbound : ∀ᶠ n in l, ∀ i, ‖u n i‖ ≤ b i)
    (hpoint : ∀ i, Tendsto (fun n => u n i) l (𝓝 (v i))) :
    ∃ w : SequenceL2 ι, (∀ i, w i = v i) ∧ Tendsto u l (𝓝 w) := by
  have hvbound : ∀ i, ‖v i‖ ≤ b i := fun i =>
    le_of_tendsto (hpoint i).norm (hbound.mono (fun n hn => hn i))
  let w : SequenceL2 ι := ⟨v, mem_sequenceL2_of_bound hb hvbound⟩
  exact ⟨w, fun _ => rfl, sequenceL2_tendsto_of_dominated hb hbound hpoint⟩

/-- The precise dominated passage to the boundary pairing. Both rows may
have different square-summable envelopes. -/
theorem dominated_pairing_tendsto {ι α : Type*} {l : Filter α} [l.NeBot]
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι)
    {u v : α → SequenceL2 ι} {u₀ v₀ : SequenceL2 ι} {b c : ι → ℝ}
    (hb : Summable (fun i => b i ^ 2)) (hc : Summable (fun i => c i ^ 2))
    (hu : ∀ᶠ n in l, ∀ i, ‖u n i‖ ≤ b i)
    (hv : ∀ᶠ n in l, ∀ i, ‖v n i‖ ≤ c i)
    (hup : ∀ i, Tendsto (fun n => u n i) l (𝓝 (u₀ i)))
    (hvp : ∀ i, Tendsto (fun n => v n i) l (𝓝 (v₀ i))) :
    Tendsto (fun n => inner ℂ (u n) (M (v n))) l (𝓝 (inner ℂ u₀ (M v₀))) :=
  pairing_tendsto M (sequenceL2_tendsto_of_dominated hb hu hup)
    (sequenceL2_tendsto_of_dominated hc hv hvp)

end Singularity
