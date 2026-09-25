import Singularity.ProjectiveSubgroupLift
import Singularity.InvolutiveKernelGeneration

/-!
# Finite projective jump laws lifted with both central signs

Each projective jump has two lifts. Give each half the original weight.
The resulting support is exactly the full inverse image of the original
support. Its weights are positive, total one, and generate the full lifted
group as a semigroup whenever the original law is admissible.
-/

noncomputable section
open Set
open scoped MatrixGroups Classical

namespace Singularity

/-- Select one of the two matrix lifts of each projective subgroup element. -/
def projectiveLiftSection (Γ : Subgroup PSL(2, ℝ)) (g : Γ) : projectiveSubgroupLift Γ :=
  (projectiveLiftProjection_surjective Γ g).choose

theorem projectiveLiftProjection_section (Γ : Subgroup PSL(2, ℝ)) (g : Γ) :
    projectiveLiftProjection Γ (projectiveLiftSection Γ g) = g :=
  (projectiveLiftProjection_surjective Γ g).choose_spec

theorem projectiveLiftProjection_sign (Γ : Subgroup PSL(2, ℝ)) :
    projectiveLiftProjection Γ (projectiveLiftSign Γ) = 1 :=
  (projectiveLiftProjection_eq_one_iff Γ _).mpr (Or.inr rfl)

/-- Exactly two lifts lie above a fixed projective element. -/
theorem projectiveLiftProjection_fibre (Γ : Subgroup PSL(2, ℝ))
    (g h : projectiveSubgroupLift Γ) (he : projectiveLiftProjection Γ g = projectiveLiftProjection Γ h) :
    g = h ∨ g = projectiveLiftSign Γ * h := by
  have hk : projectiveLiftProjection Γ (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rcases (projectiveLiftProjection_eq_one_iff Γ _).mp hk with h₀ | h₀
  · exact Or.inl (mul_inv_eq_one.mp h₀)
  · right
    have hh := congrArg (fun k => k * h) h₀
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

/-- The selected lifts are injectively labeled by the original group. -/
def projectiveLiftSectionEmbedding (Γ : Subgroup PSL(2, ℝ)) : Γ ↪ projectiveSubgroupLift Γ where
  toFun := projectiveLiftSection Γ
  inj' := Function.RightInverse.injective (projectiveLiftProjection_section Γ)

/-- The second injectively labeled lift, obtained by the central sign. -/
def projectiveLiftOtherEmbedding (Γ : Subgroup PSL(2, ℝ)) : Γ ↪ projectiveSubgroupLift Γ :=
  (projectiveLiftSectionEmbedding Γ).trans (Equiv.mulLeft (projectiveLiftSign Γ)).toEmbedding

/-- The finite support contains both lifts of every original jump. -/
def projectiveLiftSupport (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ) : Finset (projectiveSubgroupLift Γ) :=
  s.map (projectiveLiftSectionEmbedding Γ) ∪ s.map (projectiveLiftOtherEmbedding Γ)

theorem projectiveLiftSupport_disjoint (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ) :
    Disjoint (s.map (projectiveLiftSectionEmbedding Γ)) (s.map (projectiveLiftOtherEmbedding Γ)) := by
  apply Finset.disjoint_left.mpr
  intro g hg hh
  obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hg
  obtain ⟨b, hb, hf⟩ := Finset.mem_map.mp hh
  have hab : projectiveLiftSection Γ a = projectiveLiftSign Γ * projectiveLiftSection Γ b :=
    he.trans hf.symm
  have hp := congrArg (projectiveLiftProjection Γ) hab
  simp only [map_mul, projectiveLiftProjection_sign, projectiveLiftProjection_section, one_mul] at hp
  subst b
  have hbad : projectiveLiftSign Γ = 1 := by simpa using hab.symm
  exact projectiveLiftSign_ne_one Γ hbad

/-- Membership is exactly membership of the projected jump in the original support. -/
theorem mem_projectiveLiftSupport (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ)
    (g : projectiveSubgroupLift Γ) :
    g ∈ projectiveLiftSupport Γ s ↔ projectiveLiftProjection Γ g ∈ s := by
  constructor
  · intro hg
    rcases Finset.mem_union.mp hg with hg | hg
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
      change projectiveLiftProjection Γ (projectiveLiftSection Γ a) ∈ s
      rwa [projectiveLiftProjection_section]
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
      change projectiveLiftProjection Γ (projectiveLiftSign Γ * projectiveLiftSection Γ a) ∈ s
      simpa only [map_mul, projectiveLiftProjection_sign,
        projectiveLiftProjection_section, one_mul] using ha
  · intro hg
    rcases projectiveLiftProjection_fibre Γ g (projectiveLiftSection Γ (projectiveLiftProjection Γ g))
      (projectiveLiftProjection_section Γ _).symm with he | he
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨_, hg, he.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨_, hg, he.symm⟩)

/-- Set-theoretically this finite support is the entire inverse image. -/
theorem projectiveLiftSupport_coe (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ) :
    (projectiveLiftSupport Γ s : Set (projectiveSubgroupLift Γ)) =
      projectiveLiftProjection Γ ⁻¹' (s : Set Γ) := by
  ext g
  exact mem_projectiveLiftSupport Γ s g

/-- Split each original weight equally between its two lifts. -/
def projectiveLiftWeight (Γ : Subgroup PSL(2, ℝ)) (μ : Γ → ℝ)
    (g : projectiveSubgroupLift Γ) : ℝ := μ (projectiveLiftProjection Γ g) / 2

theorem projectiveLiftWeight_positive (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) :
    ∀ g ∈ projectiveLiftSupport Γ s, 0 < projectiveLiftWeight Γ μ g := by
  intro g hg
  exact div_pos (hpos _ ((mem_projectiveLiftSupport Γ s g).mp hg)) (by norm_num)

/-- Splitting into two disjoint lifts preserves the total probability mass. -/
theorem projectiveLiftWeight_mass (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ) (μ : Γ → ℝ)
    (hmass : ∑ g ∈ s, μ g = 1) :
    ∑ g ∈ projectiveLiftSupport Γ s, projectiveLiftWeight Γ μ g = 1 := by
  rw [projectiveLiftSupport, Finset.sum_union (projectiveLiftSupport_disjoint Γ s),
    Finset.sum_map, Finset.sum_map]
  change (∑ g ∈ s, μ (projectiveLiftProjection Γ (projectiveLiftSection Γ g)) / 2) +
    (∑ g ∈ s, μ (projectiveLiftProjection Γ (projectiveLiftSign Γ * projectiveLiftSection Γ g)) / 2) = 1
  simp only [map_mul, projectiveLiftProjection_sign, projectiveLiftProjection_section, one_mul,
    ← Finset.sum_div, hmass]
  norm_num

/-- The lifted support generates the full matrix lift as a semigroup. -/
theorem projectiveLiftSupport_generates (Γ : Subgroup PSL(2, ℝ)) (s : Finset Γ)
    (hne : s.Nonempty) (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    Submonoid.closure (projectiveLiftSupport Γ s : Set (projectiveSubgroupLift Γ)) = ⊤ := by
  rw [projectiveLiftSupport_coe]
  apply closure_preimage_eq_top_of_involutive_kernel (projectiveLiftProjection Γ)
    (projectiveLiftProjection_surjective Γ) (s : Set Γ) hne hgen
  intro g hg
  rcases (projectiveLiftProjection_eq_one_iff Γ g).mp hg with rfl | rfl
  · simp
  · exact projectiveLiftSign_square Γ

/-- A probability support is nonempty, so the lifted law is automatically admissible. -/
theorem projectiveLiftSupport_generates_of_mass (Γ : Subgroup PSL(2, ℝ))
    (s : Finset Γ) (μ : Γ → ℝ) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    Submonoid.closure (projectiveLiftSupport Γ s : Set (projectiveSubgroupLift Γ)) = ⊤ := by
  apply projectiveLiftSupport_generates Γ s _ hgen
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hs
  simp [hs] at hmass

end Singularity
