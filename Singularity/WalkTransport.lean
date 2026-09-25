import Singularity.InfiniteWalkProcess

/-!
# Transport of the actual random walk under a group isomorphism

Relabeling a finite jump alphabet with the same probabilities transports its
product probability law. If the labels intertwine group homomorphisms, every
position of the resulting path is the image of the original position.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical

namespace Singularity

variable {Γ Λ : Type*} [Group Γ] [Group Λ]

/-- The canonical relabeling of a finite support by a group isomorphism. -/
def mappedSupportEquiv (e : Γ ≃* Λ) (s : Finset Γ) : s ≃ s.map e.toEmbedding where
  toFun g := ⟨e g, Finset.mem_map.mpr ⟨g, g.property, rfl⟩⟩
  invFun h := ⟨e.symm h, by
    obtain ⟨g, hg, he⟩ := Finset.mem_map.mp h.property
    change e g = (h : Λ) at he
    rw [← he, e.symm_apply_apply]
    exact hg⟩
  left_inv g := by apply Subtype.ext; exact e.symm_apply_apply g
  right_inv h := by apply Subtype.ext; exact e.apply_symm_apply h

/-- Relabeling each increment gives a map between infinite sample spaces. -/
def transportWalk (s : Finset Γ) (t : Finset Λ) (e : s ≃ t) (ω : ℕ → s) : ℕ → t :=
  fun n => e (ω n)

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableSpace Λ] [MeasurableSingletonClass Λ]

omit [Group Γ] [Group Λ] [MeasurableSingletonClass Λ] in
/-- Coordinatewise relabeling is measurable. -/
theorem measurable_transportWalk (s : Finset Γ) (t : Finset Λ) (e : s ≃ t) :
    Measurable (transportWalk s t e) := by
  exact measurable_pi_lambda _ (fun n => (measurable_of_countable e).comp (measurable_pi_apply n))

omit [Group Γ] [Group Λ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableSpace Λ] [MeasurableSingletonClass Λ] in
/-- Matching weights identify the relabeled one-step distribution. -/
theorem supportJumpLaw_transport (s : Finset Γ) (t : Finset Λ) (e : s ≃ t)
    (μ : Γ → ℝ) (ν : Λ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hν : ∀ g ∈ t, 0 ≤ ν g)
    (hm : ∑ g ∈ s, μ g = 1) (hn : ∑ g ∈ t, ν g = 1)
    (hw : ∀ g : s, ν (e g) = μ g) :
    (supportJumpLaw s μ hμ hm).map e = supportJumpLaw t ν hν hn := by
  ext b
  have heq (a : s) : b = e a ↔ a = e.symm b := by
    constructor
    · intro h; simpa using (congrArg e.symm h).symm
    · rintro rfl; exact (e.apply_symm_apply b).symm
  simp only [PMF.map_apply, heq, tsum_ite_eq, supportJumpLaw_apply]
  rw [← hw (e.symm b), e.apply_symm_apply]

omit [Group Γ] [Group Λ] [MeasurableSingletonClass Λ] in
/-- The actual infinite product path law is carried to the relabeled path law. -/
theorem infiniteWalkLaw_transport (s : Finset Γ) (t : Finset Λ) (e : s ≃ t)
    (μ : Γ → ℝ) (ν : Λ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hν : ∀ g ∈ t, 0 ≤ ν g)
    (hm : ∑ g ∈ s, μ g = 1) (hn : ∑ g ∈ t, ν g = 1)
    (hw : ∀ g : s, ν (e g) = μ g) :
    Measure.map (transportWalk s t e) (infiniteWalkLaw s μ hμ hm) =
      infiniteWalkLaw t ν hν hn := by
  unfold infiniteWalkLaw transportWalk
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_of_countable e)]
  congr 1
  funext n
  rw [PMF.toMeasure_map _ _ (measurable_of_countable e),
    supportJumpLaw_transport s t e μ ν hμ hν hm hn hw]

omit [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableSpace Λ] [MeasurableSingletonClass Λ] in
/-- Intertwining each jump intertwines every position of every sample path. -/
theorem walkPosition_transport (s : Finset Γ) (t : Finset Λ) (e : s ≃ t)
    (φ : Γ →* Λ) (he : ∀ g : s, (e g : Λ) = φ g)
    (x : Γ) (n : ℕ) (ω : ℕ → s) :
    walkPosition t (φ x) n (transportWalk s t e ω) = φ (walkPosition s x n ω) := by
  induction n generalizing x ω with
  | zero => rfl
  | succ n ih =>
    simp only [walkPosition_succ]
    change walkPosition t (φ x * (e (ω 0) : Λ)) n
      (transportWalk s t e (fun k => ω (k + 1))) = _
    rw [he, ← map_mul, ih]

end Singularity
