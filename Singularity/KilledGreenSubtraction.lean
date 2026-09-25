import Singularity.RelativeGreenEntrance
import Singularity.CommonSubtraction

/-!
# Normalized killed Green columns for harmonic subtraction

The kernels used for common subtraction are actual killed Green columns.
Normalization, L² membership, and harmonicity away from the killing set and
pole are proved here. Positivity of a selected normalizer and the geometric
boundary-Harnack comparisons remain explicit inputs.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- A killed Green column normalized at o. -/
def normalizedKilledGreen (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (o z x : Γ) : ℝ :=
  killedGreen s μ A x z / killedGreen s μ A o z

theorem normalizedKilledGreen_base (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (o z : Γ)
    (hden : killedGreen s μ A o z ≠ 0) : normalizedKilledGreen s μ A o z o = 1 := div_self hden

theorem normalizedKilledGreen_nonneg (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (A : Set Γ) (o z x : Γ) : 0 ≤ normalizedKilledGreen s μ A o z x :=
  div_nonneg (killedGreen_nonneg s μ hμ A x z) (killedGreen_nonneg s μ hμ A o z)

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]

/-- A normalized killed column is square integrable, even before positivity
of its normalizer is established. -/
theorem normalizedKilledGreen_memLp (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (o z : Γ) :
    MemLp (fun x => (normalizedKilledGreen s μ A o z x : ℂ)) 2 Measure.count := by
  have hh := (killedGreenColumn_memLp s μ hμ hgap A z).const_mul ((killedGreen s μ A o z : ℂ)⁻¹)
  simpa only [normalizedKilledGreen, Complex.ofReal_div, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, mul_comm] using hh

omit [Countable Γ] in
/-- The normalized killed column is harmonic outside its killing set and pole. -/
theorem normalizedKilledGreen_harmonic (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ) (o z x : Γ)
    (hx : x ∉ A) (hxz : x ≠ z) :
    normalizedKilledGreen s μ A o z x = ∑ g ∈ s, μ g * normalizedKilledGreen s μ A o z (x*g) := by
  unfold normalizedKilledGreen
  rw [killedGreen_first_step s μ hμ hgap A hx, ite_eq_right hxz, zero_add, Finset.sum_div]
  simp only [mul_div_assoc]

/-- Finite common subtraction of L² kernels stays in L². -/
theorem commonSubtraction_memLp (k : ℕ → Γ → ℝ) (c : ℝ) (o : Γ) (f : Γ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) 2 Measure.count)
    (hk : ∀ n, MemLp (fun x => (k n x : ℂ)) 2 Measure.count) (n : ℕ) :
    MemLp (fun x => (commonSubtraction k c o f n x : ℂ)) 2 Measure.count := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    have hh := ih.sub ((hk n).const_mul ((c * commonSubtraction k c o f n o : ℝ) : ℂ))
    change MemLp (fun x => (commonSubtraction k c o f n x : ℂ) -
      ((c * commonSubtraction k c o f n o : ℝ) : ℂ) * (k n x : ℂ)) 2 Measure.count at hh
    simpa only [commonSubtraction, Complex.ofReal_sub, Complex.ofReal_mul] using hh

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ] in
/-- Common subtraction preserves harmonicity wherever all earlier kernels
and the initial function are harmonic. -/
theorem commonSubtraction_harmonic (s : Finset Γ) (μ : Γ → ℝ)
    (k : ℕ → Γ → ℝ) (c : ℝ) (o : Γ) (f : Γ → ℝ) (n : ℕ) (x : Γ)
    (hf : f x = ∑ g ∈ s, μ g * f (x*g))
    (hk : ∀ j < n, k j x = ∑ g ∈ s, μ g * k j (x*g)) :
    commonSubtraction k c o f n x = ∑ g ∈ s, μ g * commonSubtraction k c o f n (x*g) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    have hn := hk n (by omega)
    have hi := ih (fun j hj => hk j (by omega))
    simp only [commonSubtraction]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have he : (∑ g ∈ s, μ g * (c * commonSubtraction k c o f n o * k n (x*g))) =
        c * commonSubtraction k c o f n o * ∑ g ∈ s, μ g * k n (x*g) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    rw [he, ← hn, ← hi]

omit [Countable Γ] in
/-- For actual killed kernels, exclusion of each earlier killing set and pole
is sufficient to preserve harmonicity through the entire finite subtraction. -/
theorem killedGreen_commonSubtraction_harmonic (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : ℕ → Set Γ) (z : ℕ → Γ) (c : ℝ) (o : Γ) (f : Γ → ℝ) (n : ℕ) (x : Γ)
    (hf : f x = ∑ g ∈ s, μ g * f (x*g))
    (hx : ∀ j < n, x ∉ A j ∧ x ≠ z j) :
    commonSubtraction (fun j => normalizedKilledGreen s μ (A j) o (z j)) c o f n x =
      ∑ g ∈ s, μ g * commonSubtraction (fun j => normalizedKilledGreen s μ (A j) o (z j)) c o f n (x*g) := by
  apply commonSubtraction_harmonic s μ _ c o f n x hf
  intro j hj
  exact normalizedKilledGreen_harmonic s μ hμ hgap (A j) o (z j) x (hx j hj).1 (hx j hj).2

omit [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ] in
/-- Boundary-Harnack bounds for the actual killed-column residuals imply a
geometric contraction. The domain comparisons are hypotheses, not axioms. -/
theorem killedGreen_commonSubtraction_contraction (s : Finset Γ) (μ : Γ → ℝ)
    (A : ℕ → Set Γ) (z : ℕ → Γ) (o : Γ) (C : ℝ) (hC : 1 ≤ C)
    (f g : Γ → ℝ) (S : ℕ → Set Γ) (N : ℕ)
    (hden : ∀ n, killedGreen s μ (A n) o (z n) ≠ 0)
    (hfg : f o = g o) (hS : ∀ n < N, S (n+1) ⊆ S n)
    (hf : ∀ x ∈ S 0, 0 ≤ f x) (hg : ∀ x ∈ S 0, 0 ≤ g x)
    (hcompare : ∀ u ∈ ({f,g} : Set (Γ → ℝ)), ∀ n < N, ∀ x ∈ S (n+1),
      let r := commonSubtraction (fun j => normalizedKilledGreen s μ (A j) o (z j)) (1/C) o u n
      r o * normalizedKilledGreen s μ (A n) o (z n) x / C ≤ r x ∧
      r x ≤ C * (r o * normalizedKilledGreen s μ (A n) o (z n) x)) :
    ∀ x ∈ S N, |f x - g x| ≤ (1-1/C^2)^N * (f x + g x) := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hε : 1/C^2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hCp)).mpr
    nlinarith
  apply commonSubtraction_contraction (fun j => normalizedKilledGreen s μ (A j) o (z j))
    (1/C) (1/C^2) o f g S N (by positivity) hε
    (fun n => normalizedKilledGreen_base s μ (A n) o (z n) (hden n)) hfg hS hf hg
  intro u hu n hn x hx
  obtain ⟨hlo,hhi⟩ := hcompare u hu n hn x hx
  exact fractional_removal_of_comparison C _ _ _ hCp hlo hhi

end Singularity
