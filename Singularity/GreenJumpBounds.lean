import Singularity.JumpDistance
import Singularity.GreenHarnack
import Singularity.KilledGreenDecay

/-!
# Exponential Green bounds in the minimum jump distance

A shortest permitted word gives the lower bound. No transition can arrive
before the minimum length, so the spectral geometric tail gives the upper
bound. This is valid for nonsymmetric finite laws and needs no geometric
compactness or Martin-boundary identification.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- No positive-length contribution exists below the shortest possible path length. -/
theorem transitionWeight_zero_of_lt_jumpDistance (s : Finset Γ) (μ : Γ → ℝ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) (n : ℕ)
    (hn : n < jumpDistance s hgen x y) : transitionWeight s μ n x y = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  apply ite_eq_right
  intro hw
  exact (Nat.not_le_of_gt hn) (jumpDistance_le_length s hgen n w x y hw)

omit [Group Γ] in
/-- A positive finite probability support has a common positive lower bound smaller than one. -/
theorem exists_positive_jumpWeight_lower (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ g ∈ s, p ≤ μ g := by
  have hne : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hs
    simp [hs] at hmass
  obtain ⟨g, hg, hmin⟩ := s.exists_min_image μ hne
  refine ⟨min 1 (μ g) / 2, div_pos (lt_min zero_lt_one (hpos g hg)) (by norm_num), ?_, ?_⟩
  · have h := min_le_left (1 : ℝ) (μ g)
    linarith
  · intro a ha
    have h := min_le_right (1 : ℝ) (μ g)
    have hp := hpos g hg
    have hh := hmin a ha
    linarith

omit [Group Γ] in
/-- A lower bound for each jump probability gives the corresponding product lower bound. -/
theorem walkWeight_ge_pow (s : Finset Γ) (μ : Γ → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hμ : ∀ g ∈ s, p ≤ μ g) (n : ℕ) (w : WalkWord s n) : p ^ n ≤ walkWeight s μ n w := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    change p ^ (n + 1) ≤ μ w.1 * walkWeight s μ n w.2
    rw [pow_succ']
    exact mul_le_mul (hμ w.1 w.1.property) (ih w.2) (pow_nonneg hp n)
      (hp.trans (hμ w.1 w.1.property))

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]

/-- The normalized Green function dominates the weight of a shortest word. -/
theorem normalizedGreen_ge_jump_pow (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (p : ℝ) (hp : 0 ≤ p) (hlower : ∀ g ∈ s, p ≤ μ g) (x y : Γ) :
    p ^ jumpDistance s hgen x y ≤ walkGreen s μ x y / walkGreen s μ 1 1 := by
  obtain ⟨w, hw⟩ := jumpDistance_realized s hgen x y
  have h := walkGreen_word_le s μ hμ hgap _ w x y
  rw [hw] at h
  have hd : walkGreen s μ y y = walkGreen s μ 1 1 := by
    simpa only [mul_one] using walkGreen_left s μ y 1 1
  rw [hd] at h
  have hG := (zero_lt_one.trans_le (walkGreen_diag_ge_one s μ hμ hgap 1))
  exact (le_div_iff₀ hG).mpr ((mul_le_mul_of_nonneg_right
    (walkWeight_ge_pow s μ p hp hlower _ w) hG.le).trans h)

/-- The spectral tail begins at the minimum number of permitted jumps. -/
theorem walkGreen_le_jump_geometric_tail (s : Finset Γ) (μ : Γ → ℝ)
    (_hμ : ∀ g ∈ s, 0 ≤ μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (C q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ n : ℕ, ‖rightMarkov s μ ^ n‖ ≤ C * q ^ n) (x y : Γ) :
    walkGreen s μ x y ≤ C * q ^ jumpDistance s hgen x y / (1 - q) := by
  let N := jumpDistance s hgen x y
  have hs := walkGreen_summable s μ hgap x y
  have he : walkGreen s μ x y = ∑' n : ℕ, transitionWeight s μ (n + N) x y := by
    have h := hs.sum_add_tsum_nat_add N
    have hz : ∑ n ∈ Finset.range N, transitionWeight s μ n x y = 0 :=
      Finset.sum_eq_zero (fun n hn => transitionWeight_zero_of_lt_jumpDistance s μ hgen x y n
        (Finset.mem_range.mp hn))
    simpa only [hz, zero_add, walkGreen] using h.symm
  rw [he]
  calc
    _ ≤ ∑' n : ℕ, (C * q ^ N) * q ^ n := by
      apply Summable.tsum_le_tsum _ ((summable_nat_add_iff N).mpr hs)
        ((summable_geometric_of_lt_one hq hq1).mul_left (C * q ^ N))
      intro n
      calc
        _ ≤ ‖rightMarkov s μ ^ (n + N)‖ := transitionWeight_le_power_norm s μ (n + N) x y
        _ ≤ C * q ^ (n + N) := hb _
        _ = _ := by rw [pow_add]; ring
    _ = C * q ^ N / (1 - q) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]

/-- Two-sided exponential bounds in the directed support distance. -/
theorem normalizedGreen_exponential_jump_bounds (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ A p q : ℝ, 0 < A ∧ 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 ∧
      ∀ x y, p ^ jumpDistance s hgen x y ≤ walkGreen s μ x y / walkGreen s μ 1 1 ∧
        walkGreen s μ x y / walkGreen s μ 1 1 ≤ A * q ^ jumpDistance s hgen x y := by
  obtain ⟨p, hp, hp1, hl⟩ := exists_positive_jumpWeight_lower s μ hpos hmass
  obtain ⟨C, q, hC, hq, hq1, hb⟩ := markov_uniform_geometric_rate s μ hgap
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  have hG := zero_lt_one.trans_le (walkGreen_diag_ge_one s μ hμ hgap 1)
  refine ⟨C / (1 - q) / walkGreen s μ 1 1, p, q, by positivity, hp, hp1, hq, hq1, fun x y => ⟨?_, ?_⟩⟩
  · exact normalizedGreen_ge_jump_pow s μ hμ hgen hgap p hp.le hl x y
  · have h := div_le_div_of_nonneg_right
      (walkGreen_le_jump_geometric_tail s μ hμ hgen hgap C q hq.le hq1 hb x y) hG.le
    calc
      _ ≤ (C * q ^ jumpDistance s hgen x y / (1 - q)) / walkGreen s μ 1 1 := h
      _ = _ := by ring

end Singularity
