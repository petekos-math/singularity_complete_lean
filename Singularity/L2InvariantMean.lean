import Singularity.L2SetMass
import Singularity.AlmostInvariantL2
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# An invariant mean from almost invariant L² vectors

Squared masses of unit vectors are finitely additive probabilities on all
subsets. Compactness gives their ultrafilter limits. Almost invariance makes
the limiting mean right invariant. This is a genuine invariant mean, not an
operator spectral condition renamed as amenability.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical Topology

namespace Singularity

/-- Existence of a right-invariant finitely additive probability on all subsets. -/
def HasRightInvariantMean (Γ : Type*) [Group Γ] : Prop :=
  ∃ m : Set Γ → ℝ, (∀ A, 0 ≤ m A) ∧ m ∅ = 0 ∧ m univ = 1 ∧
    (∀ A B, Disjoint A B → m (A ∪ B) = m A + m B) ∧
    ∀ g : Γ, ∀ A, m ((fun x => x * g) '' A) = m A

variable {Γ : Type*} [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [Countable Γ]

/-- A fixed ultrafilter limit of the squared masses. -/
def l2InvariantMean (f : ℕ → GroupL2 Γ) (A : Set Γ) : ℝ :=
  limUnder (Ultrafilter.of (atTop : Filter ℕ)) (fun n => l2SetMass (f n) A)

/-- Compactness of [0,1] ensures that each set mass has the required ultrafilter limit. -/
theorem l2InvariantMean_tendsto (f : ℕ → GroupL2 Γ) (hf : ∀ n, ‖f n‖ = 1) (A : Set Γ) :
    Tendsto (fun n => l2SetMass (f n) A) (Ultrafilter.of (atTop : Filter ℕ)) (nhds (l2InvariantMean f A)) := by
  have hb : ∀ᶠ n in (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ), l2SetMass (f n) A ∈ Icc (0 : ℝ) 1 :=
    Eventually.of_forall (fun n => ⟨l2SetMass_nonneg _ _, by simpa [hf n] using l2SetMass_le_norm_sq (f n) A⟩)
  obtain ⟨x, hx⟩ := isCompact_Icc.ultrafilter_le_nhds'
    ((Ultrafilter.of (atTop : Filter ℕ)).map (fun n => l2SetMass (f n) A)) (mem_map.mp hb)
  exact tendsto_nhds_limUnder ⟨x, hx.2⟩

/-- Every set has nonnegative limiting mass. -/
theorem l2InvariantMean_nonneg (f : ℕ → GroupL2 Γ) (hf : ∀ n, ‖f n‖ = 1) (A : Set Γ) :
    0 ≤ l2InvariantMean f A :=
  ge_of_tendsto (l2InvariantMean_tendsto f hf A) (Eventually.of_forall (fun _ => l2SetMass_nonneg _ _))

/-- The empty set has zero limiting mass. -/
theorem l2InvariantMean_empty (f : ℕ → GroupL2 Γ) (hf : ∀ n, ‖f n‖ = 1) :
    l2InvariantMean f ∅ = 0 := by
  have h := l2InvariantMean_tendsto f hf ∅
  simp only [l2SetMass_empty] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The entire group has limiting mass one. -/
theorem l2InvariantMean_univ (f : ℕ → GroupL2 Γ) (hf : ∀ n, ‖f n‖ = 1) :
    l2InvariantMean f univ = 1 := by
  have h := l2InvariantMean_tendsto f hf univ
  simp only [l2SetMass_univ, hf, one_pow] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Disjoint finite additivity survives the ultrafilter limit. -/
theorem l2InvariantMean_union (f : ℕ → GroupL2 Γ) (hf : ∀ n, ‖f n‖ = 1)
    (A B : Set Γ) (hAB : Disjoint A B) :
    l2InvariantMean f (A ∪ B) = l2InvariantMean f A + l2InvariantMean f B := by
  have h := l2InvariantMean_tendsto f hf (A ∪ B)
  simp only [l2SetMass_union _ A B hAB] at h
  exact tendsto_nhds_unique h ((l2InvariantMean_tendsto f hf A).add (l2InvariantMean_tendsto f hf B))

variable [Group Γ] [MeasurableMul Γ]

/-- Almost invariance of vectors makes every set mass asymptotically translation invariant. -/
theorem l2SetMass_translation_tendsto (f : ℕ → GroupL2 Γ) (hf : ∀ n, ‖f n‖ = 1)
    (g : Γ) (hg : Tendsto (fun n => ‖rightTranslation g (f n) - f n‖) atTop (nhds 0))
    (A : Set Γ) : Tendsto (fun n => l2SetMass (f n) ((fun x => x * g) '' A) - l2SetMass (f n) A)
      atTop (nhds 0) := by
  apply squeeze_zero_norm (fun n => ?_) (by simpa using hg.const_mul 2)
  rw [Real.norm_eq_abs, ← l2SetMass_rightTranslation]
  have h := l2SetMass_sub_le (rightTranslation g (f n)) (f n) A
  simpa only [rightTranslation_norm, hf, one_add_one_eq_two] using h

/-- The limit mean is invariant under every translation that almost fixes the vectors. -/
theorem l2InvariantMean_right_invariant (f : ℕ → GroupL2 Γ) (hf : ∀ n, ‖f n‖ = 1)
    (g : Γ) (hg : Tendsto (fun n => ‖rightTranslation g (f n) - f n‖) atTop (nhds 0))
    (A : Set Γ) : l2InvariantMean f ((fun x => x * g) '' A) = l2InvariantMean f A := by
  have h := (l2SetMass_translation_tendsto f hf g hg A).mono_left (Ultrafilter.of_le atTop)
  have hl := (l2InvariantMean_tendsto f hf ((fun x => x * g) '' A)).sub (l2InvariantMean_tendsto f hf A)
  exact sub_eq_zero.mp (tendsto_nhds_unique hl h)

/-- Almost invariant unit vectors supply a right-invariant finitely additive probability. -/
theorem hasRightInvariantMean_of_almostInvariantL2 (f : ℕ → GroupL2 Γ)
    (hf : ∀ n, ‖f n‖ = 1)
    (hinv : ∀ g : Γ, Tendsto (fun n => ‖rightTranslation g (f n) - f n‖) atTop (nhds 0)) :
    HasRightInvariantMean Γ :=
  ⟨l2InvariantMean f, l2InvariantMean_nonneg f hf, l2InvariantMean_empty f hf,
    l2InvariantMean_univ f hf, l2InvariantMean_union f hf,
    fun g A => l2InvariantMean_right_invariant f hf g (hinv g) A⟩

omit [Countable Γ] in
/-- The nonamenability spectral-gap implication for the original right Markov operator. -/
theorem rightMarkov_gap_of_no_rightInvariantMean (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (hnon : ¬HasRightInvariantMean Γ) :
    spectralRadius ℂ (rightMarkov s μ) < 1 := by
  by_contra hgap
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  obtain ⟨f, hf, hinv⟩ := exists_almostInvariantL2_of_no_gap s μ hpos hmass hgen hgap
  exact hnon (hasRightInvariantMean_of_almostInvariantL2 f hf hinv)

end Singularity
