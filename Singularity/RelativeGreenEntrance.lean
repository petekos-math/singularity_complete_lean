import Singularity.EntranceRepresentation
import Singularity.GreenSeparator

/-!
# Entrance identities inside an already killed domain

Paths may be killed on A before stopping on B. Their first-entrance weights are
exactly F_(A∪B)(x,b) for b in B\A. L² Dirichlet uniqueness gives the exact
relative Green decomposition, with absolutely convergent infinite sums.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

/-- A killed path cannot end in the killing set. -/
theorem killedGreen_target_mem {Γ : Type*} [Group Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x y : Γ) (hy : y ∈ A) :
    killedGreen s μ A x y = 0 := by
  simp [killedGreen, killedWeight, hy]

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (A B : Set Γ)

include hμ hgap in
/-- The difference of the two killed columns is harmonic outside A∪B. -/
theorem killedGreenColumn_difference_harmonic (y x : Γ) (hx : x ∉ A ∪ B) :
    rightMarkov s μ (killedGreenColumn s μ hμ hgap A y - killedGreenColumn s μ hμ hgap (A ∪ B) y) x =
      (killedGreenColumn s μ hμ hgap A y - killedGreenColumn s μ hμ hgap (A ∪ B) y) x := by
  have ha : x ∉ A := fun h => hx (Or.inl h)
  have h₁ := killedGreenColumn_defect s μ hμ hgap A y ha
  have h₂ := killedGreenColumn_defect s μ hμ hgap (A ∪ B) y hx
  simp only [counting_sub_apply] at h₁ h₂
  rw [map_sub, counting_sub_apply, counting_sub_apply]
  linear_combination h₂ - h₁

/-- Extending the A-killed column from A∪B recovers exactly the trajectories
removed by adding B to the killing set. -/
theorem relativeGreen_entrance_extension (y : Γ) :
    firstEntranceExtension s μ hμ hmass hgap (A ∪ B) (killedGreenColumn s μ hμ hgap A y) =
      killedGreenColumn s μ hμ hgap A y - killedGreenColumn s μ hμ hgap (A ∪ B) y := by
  apply harmonic_eq_of_boundary_eq (rightMarkov s μ) (rightMarkov_contraction s μ hμ hmass) hgap (A ∪ B)
  · intro x hx
    have hh := congrArg (fun v : supportedL2 (A ∪ B) => (v : GroupL2 Γ) x)
      (entranceOperator_boundary s μ hμ hmass hgap (A ∪ B)
        (supportedRestriction (A ∪ B) (killedGreenColumn s μ hμ hgap A y)))
    rw [supportedRestriction_apply (A ∪ B) _ ⟨x,hx⟩,
      supportedRestriction_apply (A ∪ B) _ ⟨x,hx⟩] at hh
    rw [counting_sub_apply, killedGreenColumn_boundary s μ hμ hgap (A ∪ B) y hx, sub_zero]
    exact hh
  · intro x hx
    exact entranceOperator_harmonic s μ hμ hmass hgap (A ∪ B) _ hx
  · exact fun x hx => killedGreenColumn_difference_harmonic s μ hμ hgap A B y x hx

include hμ hmass hgap in
/-- The relative entrance contribution is absolutely summable on the full group. -/
theorem relativeGreen_entrance_summable (x y : Γ) :
    Summable (fun b : Γ => firstEntranceKernel s μ (A ∪ B) x b * killedGreen s μ A b y) := by
  have hh := firstEntranceExtension_summable_norm s μ hμ hmass hgap (A ∪ B)
    (killedGreenColumn s μ hμ hgap A y) x
  simpa only [killedGreenColumn_apply, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (firstEntranceKernel_nonneg s μ hμ _ _ _) (killedGreen_nonneg s μ hμ _ _ _))] using hh

include hμ hmass hgap in
/-- Exact entrance decomposition with prior killing on A. -/
theorem killedGreen_entrance_decomposition (x y : Γ) :
    killedGreen s μ A x y = killedGreen s μ (A ∪ B) x y +
      ∑' b : Γ, firstEntranceKernel s μ (A ∪ B) x b * killedGreen s μ A b y := by
  have hh := congrArg (fun f : GroupL2 Γ => f x) (relativeGreen_entrance_extension s μ hμ hmass hgap A B y)
  rw [firstEntranceExtension_eq_tsum, counting_sub_apply] at hh
  simp only [killedGreenColumn_apply, ← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub] at hh
  have he := Complex.ofReal_injective hh
  linarith

include hμ hmass hgap in
/-- Only points of B outside the previous killing set contribute. -/
theorem killedGreen_entrance_decomposition_subtype (x y : Γ) :
    killedGreen s μ A x y = killedGreen s μ (A ∪ B) x y +
      ∑' b : ↥(B \ A : Set Γ), firstEntranceKernel s μ (A ∪ B) x b * killedGreen s μ A b y := by
  rw [killedGreen_entrance_decomposition s μ hμ hmass hgap A B x y]
  congr 1
  symm
  apply tsum_subtype_eq_of_support_subset (s := B \ A)
    (f := fun b : Γ => firstEntranceKernel s μ (A ∪ B) x b * killedGreen s μ A b y)
  intro b hb
  change firstEntranceKernel s μ (A ∪ B) x b * killedGreen s μ A b y ≠ 0 at hb
  by_cases ha : b ∈ A
  · exact (hb (by rw [killedGreen_of_mem s μ A ha, mul_zero])).elim
  · refine ⟨?_, ha⟩
    by_contra hB
    exact hb (by rw [firstEntranceKernel_eq_zero_of_notMem s μ (A ∪ B) x b (by simp [ha,hB]), zero_mul])

include hμ hmass hgap in
/-- The exact relative entrance contribution is bounded by the relative Green kernel. -/
theorem relativeGreen_entrance_sum_le (x y : Γ) :
    (∑' b : Γ, firstEntranceKernel s μ (A ∪ B) x b * killedGreen s μ A b y) ≤ killedGreen s μ A x y := by
  rw [killedGreen_entrance_decomposition s μ hμ hmass hgap A B x y]
  exact le_add_of_nonneg_left (killedGreen_nonneg s μ hμ _ _ _)

include hμ hmass hgap in
/-- A finite additional stopping set gives a finite relative entrance sum. -/
theorem killedGreen_finite_entrance_decomposition (B : Finset Γ) (x y : Γ) :
    killedGreen s μ A x y = killedGreen s μ (A ∪ (B : Set Γ)) x y +
      ∑ b ∈ B, firstEntranceKernel s μ (A ∪ (B : Set Γ)) x b * killedGreen s μ A b y := by
  rw [killedGreen_entrance_decomposition s μ hμ hmass hgap A (B : Set Γ) x y]
  congr 1
  apply tsum_eq_sum
  intro b hb
  by_cases ha : b ∈ A
  · rw [killedGreen_of_mem s μ A ha, mul_zero]
  · rw [firstEntranceKernel_eq_zero_of_notMem s μ (A ∪ (B : Set Γ)) x b (by simp [ha, hb]), zero_mul]

include hμ hmass hgap in
/-- Adding killing can only decrease the Green kernel. -/
theorem killedGreen_antitone (hAB : A ⊆ B) (x y : Γ) :
    killedGreen s μ B x y ≤ killedGreen s μ A x y := by
  have hh := killedGreen_entrance_decomposition s μ hμ hmass hgap A B x y
  rw [Set.union_eq_right.mpr hAB] at hh
  have hs : 0 ≤ ∑' b : Γ, firstEntranceKernel s μ B x b * killedGreen s μ A b y :=
    tsum_nonneg (fun b => mul_nonneg (firstEntranceKernel_nonneg s μ hμ B x b) (killedGreen_nonneg s μ hμ A b y))
  linarith

include hμ hmass hgap in
/-- Relative singleton renewal uses the probability of reaching u before A. -/
theorem killedGreen_singleton_renewal (x u : Γ) :
    killedGreen s μ A x u = firstEntranceKernel s μ (A ∪ {u}) x u * killedGreen s μ A u u := by
  have hh := killedGreen_finite_entrance_decomposition s μ hμ hmass hgap A {u} x u
  simp only [Finset.coe_singleton, Finset.sum_singleton] at hh
  rw [killedGreen_target_mem s μ (A ∪ {u}) x u (Or.inr (Set.mem_singleton u)), zero_add] at hh
  exact hh

include hμ hmass hgap in
/-- The lower multiplicative Green inequality holds inside every killed domain. -/
theorem killedGreen_product_le (x u y : Γ) :
    killedGreen s μ A x u * killedGreen s μ A u y ≤
      killedGreen s μ A u u * killedGreen s μ A x y := by
  have hh := killedGreen_finite_entrance_decomposition s μ hμ hmass hgap A {u} x y
  simp only [Finset.coe_singleton, Finset.sum_singleton] at hh
  have hb : firstEntranceKernel s μ (A ∪ {u}) x u * killedGreen s μ A u y ≤ killedGreen s μ A x y := by
    linarith [killedGreen_nonneg s μ hμ (A ∪ {u}) x y]
  rw [killedGreen_singleton_renewal s μ hμ hmass hgap A x u]
  calc
    _ = killedGreen s μ A u u * (firstEntranceKernel s μ (A ∪ {u}) x u * killedGreen s μ A u y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (killedGreen_nonneg s μ hμ A u u)

end Singularity
