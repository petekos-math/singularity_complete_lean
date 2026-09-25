import Singularity.CocompactExcessAncona
import Singularity.NaimSubsequence

/-!
# Positive finite bounds on off-diagonal Naïm quotients

The lower bound is universal. In the cocompact setting a fixed positive disk
separation gives the upper bound via the proved Ancona inequality. Thus any
off-diagonal disk approach has a positive finite subsequential limit. This does
not assert uniqueness or existence of the full boundary kernel.
-/

noncomputable section
open Filter
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- The first-hit inequality bounds every finite Naïm quotient away from zero. -/
theorem finiteNaimQuotient_lower {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (o x y : Γ) :
    (walkGreen s μ 1 1)⁻¹ ≤ finiteNaimQuotient s μ o x y := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hdiag : walkGreen s μ o o = walkGreen s μ 1 1 := by
    simpa only [mul_one] using walkGreen_left s μ o 1 1
  have hh := walkGreen_product_le s μ (fun g hg => (hpos g hg).le) hmass hgap x o y
  rw [hdiag] at hh
  unfold finiteNaimQuotient
  apply (le_div_iff₀ (naim_normalizer_pos s μ hpos hgen hgap o x y)).mpr
  have hG := walkGreen_pos s μ hpos hgen hgap (1:Γ) 1
  have hi := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hG).le
  simpa only [← mul_assoc, inv_mul_cancel₀ hG.ne', one_mul] using hi

/-- Disk separation gives a compact interval containing the actual finite quotients. -/
theorem cocompact_finiteNaimQuotient_bounds (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℝ, 0 < H ∧ ∀ x y : Γ,
      δ ≤ dist (halfPlaneCayley (x • UpperHalfPlane.I)) (halfPlaneCayley (y • UpperHalfPlane.I)) →
      finiteNaimQuotient s μ 1 x y ∈ Set.Icc (walkGreen s μ 1 1)⁻¹ H := by
  obtain ⟨H, hH, hb⟩ := cocompact_disk_separated_green_product_bound Γ s μ hpos hmass hgen hgap δ hδ
  refine ⟨H, hH, ?_⟩
  intro x y hsep
  refine ⟨finiteNaimQuotient_lower s μ hpos hmass hgen hgap 1 x y, ?_⟩
  exact (div_le_iff₀ (naim_normalizer_pos s μ hpos hgen hgap 1 x y)).mpr (hb x y hsep)

/-- Distinct disk limits give a positive uniform separation eventually. -/
theorem eventually_cayley_separated {α : Type*} {l : Filter α} (x y : α → ℍ)
    (a b : ℂ) (hab : a ≠ b)
    (hx : Tendsto (fun n => halfPlaneCayley (x n)) l (𝓝 a))
    (hy : Tendsto (fun n => halfPlaneCayley (y n)) l (𝓝 b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in l, δ ≤ dist (halfPlaneCayley (x n)) (halfPlaneCayley (y n)) := by
  have hd : 0 < dist a b := dist_pos.mpr hab
  refine ⟨dist a b / 2, by positivity, ?_⟩
  exact ((hx.dist hy).eventually (lt_mem_nhds (by linarith : dist a b / 2 < dist a b))).mono
    (fun _ h => h.le)

/-- Every off-diagonal disk approach admits a positive finite subsequential
Naïm quotient limit, without current or density assumptions. -/
theorem cocompact_positive_naim_subsequence (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : ℕ → Γ)
    (a b : ℂ) (hab : a ≠ b)
    (hx : Tendsto (fun n => halfPlaneCayley (x n • UpperHalfPlane.I)) atTop (𝓝 a))
    (hy : Tendsto (fun n => halfPlaneCayley (y n • UpperHalfPlane.I)) atTop (𝓝 b)) :
    ∃ θ : ℝ, 0 < θ ∧ (walkGreen s μ 1 1)⁻¹ ≤ θ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => finiteNaimQuotient s μ 1 (x (φ n)) (y (φ n))) atTop (𝓝 θ) := by
  obtain ⟨δ, hδ, hsep⟩ := eventually_cayley_separated
    (fun n => x n • UpperHalfPlane.I) (fun n => y n • UpperHalfPlane.I) a b hab hx hy
  obtain ⟨H, hH, hb⟩ := cocompact_finiteNaimQuotient_bounds Γ s μ hpos hmass hgen hgap δ hδ
  have he : ∀ᶠ n in atTop, finiteNaimQuotient s μ 1 (x n) (y n) ∈
      Set.Icc (walkGreen s μ 1 1)⁻¹ H := hsep.mono (fun n hn => hb (x n) (y n) hn)
  obtain ⟨θ, hθ, φ, hφ, ht⟩ := isCompact_Icc.tendsto_subseq' he.frequently
  exact ⟨θ, (inv_pos.mpr (walkGreen_pos s μ hpos hgen hgap 1 1)).trans_le hθ.1,
    hθ.1, φ, hφ, ht⟩

end Singularity
