import Singularity.ProjectiveLiftSupport
import Singularity.WalkTransport

/-!
# Projecting the lifted random walk to the original projective law

The two signed lifts of each jump project to the original one-step
probability. The same projection preserves the infinite iid path law and
intertwines every path position, so the lifting construction changes neither
the projective walk nor its geometric trajectory.
-/

noncomputable section
open MeasureTheory Set
open scoped MatrixGroups UpperHalfPlane Classical ENNReal

namespace Singularity

/-- The first support-valued matrix lift. -/
def projectiveSupportFirst (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ) (g : s) : projectiveLiftSupport Γ s :=
  ⟨projectiveLiftSection Γ g, (mem_projectiveLiftSupport Γ s _).mpr (by
    rw [projectiveLiftProjection_section]
    exact g.property)⟩

/-- The other support-valued matrix lift. -/
def projectiveSupportSecond (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ) (g : s) : projectiveLiftSupport Γ s :=
  ⟨projectiveLiftSign Γ * projectiveLiftSection Γ g, (mem_projectiveLiftSupport Γ s _).mpr (by
    rw [map_mul, projectiveLiftProjection_sign, projectiveLiftProjection_section, one_mul]
    exact g.property)⟩

/-- Project a support-valued signed jump to its projective jump. -/
def projectiveSupportProjection (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ)
    (g : projectiveLiftSupport Γ s) : s :=
  ⟨projectiveLiftProjection Γ g, (mem_projectiveLiftSupport Γ s g).mp g.property⟩

theorem projectiveSupportFirst_ne_second (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ) (g : s) :
    projectiveSupportFirst Γ s g ≠ projectiveSupportSecond Γ s g := by
  intro he
  have hh := congrArg Subtype.val he
  change projectiveLiftSection Γ g = projectiveLiftSign Γ * projectiveLiftSection Γ g at hh
  exact projectiveLiftSign_ne_one Γ (by simpa using hh.symm)

/-- Each support fibre consists of exactly the two selected signs. -/
theorem projectiveSupportProjection_fibre (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ)
    (g : projectiveLiftSupport Γ s) (h : s) :
    projectiveSupportProjection Γ s g = h ↔
      g = projectiveSupportFirst Γ s h ∨ g = projectiveSupportSecond Γ s h := by
  constructor
  · intro he
    have hh : projectiveLiftProjection Γ g = (h : Γ) := congrArg Subtype.val he
    rcases projectiveLiftProjection_fibre Γ g (projectiveLiftSection Γ h)
      (hh.trans (projectiveLiftProjection_section Γ h).symm) with h₀ | h₀
    · exact Or.inl (Subtype.ext h₀)
    · exact Or.inr (Subtype.ext h₀)
  · rintro (rfl | rfl) <;> apply Subtype.ext
    · exact projectiveLiftProjection_section Γ h
    · exact (map_mul (projectiveLiftProjection Γ) _ _).trans (by
        rw [projectiveLiftProjection_sign, projectiveLiftProjection_section, one_mul])

set_option backward.isDefEq.respectTransparency false in
/-- Projection of the two half-weight atoms gives exactly the original jump law. -/
theorem supportJumpLaw_projective_projection (Γ : Subgroup PSL(2, ℝ))
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1) :
    (supportJumpLaw (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ)
      (fun g hg => (projectiveLiftWeight_positive Γ s μ hpos g hg).le)
      (projectiveLiftWeight_mass Γ s μ hmass)).map (projectiveSupportProjection Γ s) =
        supportJumpLaw s μ (fun g hg => (hpos g hg).le) hmass := by
  let p := supportJumpLaw (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ)
    (fun g hg => (projectiveLiftWeight_positive Γ s μ hpos g hg).le)
    (projectiveLiftWeight_mass Γ s μ hmass)
  ext b
  let : DecidableEq s := fun x y => Classical.propDecidable (x = y)
  change (p.map (projectiveSupportProjection Γ s)) b = _
  rw [PMF.map_apply]
  have he : (fun a => if b = projectiveSupportProjection Γ s a then p a else 0) =
      (fun a => (if a = projectiveSupportFirst Γ s b then p (projectiveSupportFirst Γ s b) else 0) +
        (if a = projectiveSupportSecond Γ s b then p (projectiveSupportSecond Γ s b) else 0)) := by
    funext a
    have hh : b = projectiveSupportProjection Γ s a ↔
        a = projectiveSupportFirst Γ s b ∨ a = projectiveSupportSecond Γ s b :=
      eq_comm.trans (projectiveSupportProjection_fibre Γ s a b)
    simp only [hh]
    by_cases h₁ : a = projectiveSupportFirst Γ s b
    · subst a
      simp [projectiveSupportFirst_ne_second]
    · by_cases h₂ : a = projectiveSupportSecond Γ s b
      · subst a
        simp [h₁]
      · simp [h₁, h₂]
  have hs := congrArg tsum he
  apply hs.trans
  rw [ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq]
  change ENNReal.ofReal (μ (projectiveLiftProjection Γ (projectiveLiftSection Γ b)) / 2) +
    ENNReal.ofReal (μ (projectiveLiftProjection Γ (projectiveLiftSign Γ * projectiveLiftSection Γ b)) / 2) =
      ENNReal.ofReal (μ b)
  rw [map_mul, projectiveLiftProjection_sign, projectiveLiftProjection_section, one_mul,
    ← ENNReal.ofReal_add (div_nonneg (hpos b b.property).le (by norm_num))
      (div_nonneg (hpos b b.property).le (by norm_num))]
  congr 1
  ring

/-- Project each jump in an infinite signed path. -/
def projectiveWalkProjection (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ)
    (ω : ℕ → projectiveLiftSupport Γ s) : ℕ → s :=
  fun n => projectiveSupportProjection Γ s (ω n)

section Measures
variable (Γ : Subgroup PSL(2, ℝ)) [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableSpace (projectiveSubgroupLift Γ)] [MeasurableSingletonClass (projectiveSubgroupLift Γ)]

omit [MeasurableSingletonClass Γ] in
theorem measurable_projectiveWalkProjection (s : Finset Γ) :
    Measurable (projectiveWalkProjection Γ s) := by
  exact measurable_pi_lambda _ (fun n =>
    (measurable_of_countable (projectiveSupportProjection Γ s)).comp (measurable_pi_apply n))

omit [MeasurableSingletonClass Γ] in
/-- The projected iid path law is the original projective random-walk law. -/
theorem infiniteWalkLaw_projective_projection (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1) :
    Measure.map (projectiveWalkProjection Γ s)
      (infiniteWalkLaw (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ)
        (fun g hg => (projectiveLiftWeight_positive Γ s μ hpos g hg).le)
        (projectiveLiftWeight_mass Γ s μ hmass)) =
      infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass := by
  unfold infiniteWalkLaw projectiveWalkProjection
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_of_countable (projectiveSupportProjection Γ s))]
  congr 1
  funext n
  rw [PMF.toMeasure_map _ _ (measurable_of_countable (projectiveSupportProjection Γ s)),
    supportJumpLaw_projective_projection Γ s μ hpos hmass]

end Measures

/-- Every projected position is the projection of the lifted position. -/
theorem walkPosition_projective_projection (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ)
    (x : projectiveSubgroupLift Γ) (n : ℕ) (ω : ℕ → projectiveLiftSupport Γ s) :
    walkPosition s (projectiveLiftProjection Γ x) n (projectiveWalkProjection Γ s ω) =
      projectiveLiftProjection Γ (walkPosition (projectiveLiftSupport Γ s) x n ω) := by
  induction n generalizing x ω with
  | zero => rfl
  | succ n ih =>
    simp only [walkPosition_succ]
    change walkPosition s (projectiveLiftProjection Γ x * projectiveLiftProjection Γ (ω 0)) n
      (projectiveWalkProjection Γ s (fun k => ω (k + 1))) = _
    rw [← map_mul, ih]

/-- The two coupled walks have identical geometric trajectories at every time. -/
theorem projective_walk_hyperbolic_trajectory (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ)
    (n : ℕ) (ω : ℕ → projectiveLiftSupport Γ s) (z : ℍ) :
    walkPosition s 1 n (projectiveWalkProjection Γ s ω) • z =
      walkPosition (projectiveLiftSupport Γ s) 1 n ω • z := by
  rw [← map_one (projectiveLiftProjection Γ), walkPosition_projective_projection]
  rfl

end Singularity
