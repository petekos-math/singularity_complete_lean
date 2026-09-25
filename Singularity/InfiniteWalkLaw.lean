import Singularity.FiniteWalkLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# The infinite random-walk probability space

The sample space is the sequence of finite-support jumps. Its law is the
countable product of the jump distribution. Finite prefixes are identified
with the recursive words used by the existing path and Green-kernel proofs.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace Singularity

/-- Finite recursive words carry the discrete measurable structure. -/
instance walkWordMeasurableSpace (S : Type*) (n : ℕ) : MeasurableSpace (WalkWord S n) := ⊤

instance walkWordMeasurableSingletonClass (S : Type*) (n : ℕ) :
    MeasurableSingletonClass (WalkWord S n) := ⟨fun _ => trivial⟩

/-- Convert the recursive finite word into its chronologically indexed tuple. -/
def walkWordEquivFin (S : Type*) : (n : ℕ) → WalkWord S n ≃ (Fin n → S)
  | 0 => (show PUnit ≃ (Fin 0 → S) from Equiv.ofUnique _ _)
  | n + 1 => (Equiv.prodCongr (Equiv.refl S) (walkWordEquivFin S n)).trans
      (Fin.consEquiv (fun _ => S))

/-- Chronological coordinates respect the recursive head and tail. -/
theorem walkWordEquivFin_succ (S : Type*) (n : ℕ) (g : S) (w : WalkWord S n) :
    walkWordEquivFin S (n + 1) (g, w) = Fin.cons g (walkWordEquivFin S n w) := rfl

/-- The first n jumps of an infinite sample, in the existing recursive format. -/
def walkPrefix (S : Type*) (n : ℕ) (ω : ℕ → S) : WalkWord S n :=
  (walkWordEquivFin S n).symm (fun i => ω i.val)

/-- The recursion reads the first jump, then the prefix of the shifted sample. -/
theorem walkPrefix_succ (S : Type*) (n : ℕ) (ω : ℕ → S) :
    walkPrefix S (n + 1) ω = (ω 0, walkPrefix S n (fun k => ω (k + 1))) := rfl

/-- Finite prefix extraction is measurable. -/
theorem measurable_walkPrefix (S : Type*) [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (n : ℕ) : Measurable (walkPrefix S n) := by
  exact (measurable_of_countable (walkWordEquivFin S n).symm).comp (by fun_prop)

variable {Γ : Type*} [Group Γ]

omit [Group Γ] in
/-- Recursive word weights equal products of the coordinate jump weights. -/
theorem walkWeight_eq_fin_prod (s : Finset Γ) (μ : Γ → ℝ) (n : ℕ) (w : WalkWord s n) :
    walkWeight s μ n w = ∏ i : Fin n, μ (walkWordEquivFin s n w i) := by
  induction n with
  | zero => simp [walkWeight]
  | succ n ih =>
    rcases w with ⟨g, w⟩
    change μ g * walkWeight s μ n w = ∏ i : Fin (n + 1), μ (walkWordEquivFin s (n + 1) (g, w) i)
    rw [walkWordEquivFin_succ, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, ih w]

omit [Group Γ]

/-- The probability mass function of a single support-valued jump. -/
def supportJumpLaw (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) : PMF s :=
  PMF.ofFintype (fun g => ENNReal.ofReal (μ g)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun (g : s) _ => hμ g g.property)]
    simp only [Finset.univ_eq_attach, Finset.sum_attach, hmass, ENNReal.ofReal_one])

theorem supportJumpLaw_apply (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (g : s) :
    supportJumpLaw s μ hμ hmass g = ENNReal.ofReal (μ g) := rfl

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- The infinite law of independent identically distributed support-valued jumps. -/
def infiniteWalkLaw (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) : Measure (ℕ → s) :=
  Measure.infinitePi (fun _ : ℕ => (supportJumpLaw s μ hμ hmass).toMeasure)

instance infiniteWalkLaw_probability (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) :
    IsProbabilityMeasure (infiniteWalkLaw s μ hμ hmass) := by
  unfold infiniteWalkLaw
  infer_instance

omit [MeasurableSingletonClass Γ] in
/-- The jump coordinates are independent under the constructed infinite law. -/
theorem infiniteWalkLaw_independent (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) :
    iIndepFun (fun n (ω : ℕ → s) => ω n) (infiniteWalkLaw s μ hμ hmass) :=
  iIndepFun_infinitePi (X := fun _ ω => ω) (fun _ => measurable_id)

omit [MeasurableSingletonClass Γ] in
/-- Every coordinate has the specified one-step jump distribution. -/
theorem infiniteWalkLaw_coordinate (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) :
    Measure.map (fun ω : ℕ → s => ω n) (infiniteWalkLaw s μ hμ hmass) =
      (supportJumpLaw s μ hμ hmass).toMeasure := Measure.infinitePi_map_eval _ _

omit [MeasurableSingletonClass Γ] in
/-- The first n coordinates have the finite product distribution. -/
theorem infiniteWalkLaw_firstCoordinates (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) :
    Measure.map (fun (ω : ℕ → s) (i : Fin n) => ω i.val) (infiniteWalkLaw s μ hμ hmass) =
      Measure.pi (fun _ : Fin n => (supportJumpLaw s μ hμ hmass).toMeasure) := by
  rw [infiniteWalkLaw, Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => Fin.ext h),
    Measure.infinitePi_eq_pi]

omit [MeasurableSingletonClass Γ] in
/-- Removing finitely many initial jumps preserves the infinite jump law. -/
theorem infiniteWalkLaw_shift (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (k : ℕ) :
    Measure.map (fun (ω : ℕ → s) n => ω (n + k)) (infiniteWalkLaw s μ hμ hmass) =
      infiniteWalkLaw s μ hμ hmass :=
  Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => Nat.add_right_cancel h)

/-- Each finite prefix has exactly the previously constructed word probability. -/
theorem infiniteWalkLaw_prefix_probability (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (n : ℕ) (w : WalkWord s n) :
    infiniteWalkLaw s μ hμ hmass {ω | walkPrefix s n ω = w} =
      ENNReal.ofReal (walkWeight s μ n w) := by
  have he : {ω : ℕ → s | walkPrefix s n ω = w} =
      (fun (ω : ℕ → s) (i : Fin n) => ω i.val) ⁻¹' {walkWordEquivFin s n w} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, walkPrefix,
      Equiv.symm_apply_eq]
  rw [he, ← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    infiniteWalkLaw_firstCoordinates, Measure.pi_singleton, walkWeight_eq_fin_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun (i : Fin n) _ => hμ _ (walkWordEquivFin s n w i).property)]
  apply Finset.prod_congr rfl
  intro i _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), supportJumpLaw_apply]

/-- Prefix pushforwards identify the full finite-dimensional word law. -/
theorem infiniteWalkLaw_prefix (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (n : ℕ) :
    Measure.map (walkPrefix s n) (infiniteWalkLaw s μ hμ hmass) =
      (finiteWalkLaw s μ hμ hmass n).toMeasure := by
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply (measurable_walkPrefix s n) (measurableSet_singleton w),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton w), finiteWalkLaw_apply]
  exact infiniteWalkLaw_prefix_probability s μ hμ hmass n w

end Singularity
