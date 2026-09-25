import Singularity.FiniteIndexFreeLength

/-!
# Undistortion of infinite-order elements in virtually free groups

A lower bound on powers of g^m extends to all powers of g: write the exponent
as mq+r and bound the remainder by m times the length of g. Together with the
finite-index free-subgroup estimate, this supplies the full linear word-growth
hypothesis without assuming it separately.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

variable {G : Type*} [Group G]

/-- Word length is subadditive on products. -/
theorem wordDistance_one_mul_le (s : Finset G) (hgen : Submonoid.closure (s : Set G) = ⊤)
    (g h : G) : wordDistance s hgen 1 (g * h) ≤ wordDistance s hgen 1 g + wordDistance s hgen 1 h := by
  have htri := wordDistance_triangle s hgen 1 g (g * h)
  have he : wordDistance s hgen g (g * h) = wordDistance s hgen 1 h := by
    simpa only [mul_one] using wordDistance_left s hgen g 1 h
  rwa [he] at htri

/-- The length of g^n is at most n times the length of g. -/
theorem wordDistance_pow_le (s : Finset G) (hgen : Submonoid.closure (s : Set G) = ⊤)
    (g : G) (n : ℕ) : wordDistance s hgen 1 (g ^ n) ≤ n * wordDistance s hgen 1 g := by
  induction n with
  | zero => simp only [pow_zero, Nat.zero_mul, Nat.le_zero]; exact (wordDistance_eq_zero_iff s hgen 1 1).mpr rfl
  | succ n ih =>
    rw [pow_succ]
    exact (wordDistance_one_mul_le s hgen _ _).trans (by simpa [Nat.succ_mul] using Nat.add_le_add_right ih (wordDistance s hgen 1 g))

/-- Linear growth for one positive power implies linear growth for the original element. -/
theorem linear_word_growth_of_power (s : Finset G) (hgen : Submonoid.closure (s : Set G) = ⊤)
    (g : G) (m : ℕ) (hm : 0 < m) (κ : ℝ) (hκ : 0 < κ)
    (hpow : ∀ n : ℕ, κ * n ≤ (wordDistance s hgen 1 ((g ^ m) ^ n) : ℝ)) :
    ∃ c E : ℝ, 0 < c ∧ 0 ≤ E ∧ ∀ n : ℕ,
      c * n - E ≤ (wordDistance s hgen 1 (g ^ n) : ℝ) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨κ / m, κ + (m : ℝ) * wordDistance s hgen 1 g, div_pos hκ hmp, by positivity, fun n => ?_⟩
  let q := n / m
  let r := n % m
  have hdiv : m * q + r = n := Nat.div_add_mod n m
  have hr : r < m := Nat.mod_lt n hm
  have he : (g ^ m) ^ q * g ^ r = g ^ n := by rw [← pow_mul, ← pow_add, hdiv]
  have htail : wordDistance s hgen 1 ((g ^ m) ^ q) ≤
      wordDistance s hgen 1 (g ^ n) + m * wordDistance s hgen 1 g := by
    have ht := wordDistance_triangle s hgen 1 (g ^ n) ((g ^ m) ^ q)
    rw [wordDistance_symm s hgen (g ^ n) ((g ^ m) ^ q)] at ht
    have hc : wordDistance s hgen ((g ^ m) ^ q) (g ^ n) = wordDistance s hgen 1 (g ^ r) := by
      rw [← he]
      simpa only [mul_one] using wordDistance_left s hgen ((g ^ m) ^ q) 1 (g ^ r)
    rw [hc] at ht
    exact ht.trans (Nat.add_le_add_left ((wordDistance_pow_le s hgen g r).trans
      (Nat.mul_le_mul_right _ hr.le)) _)
  have htailR : (wordDistance s hgen 1 ((g ^ m) ^ q) : ℝ) ≤
      (wordDistance s hgen 1 (g ^ n) : ℝ) + (m : ℝ) * wordDistance s hgen 1 g := by
    exact_mod_cast htail
  have hn : (n : ℝ) ≤ (m : ℝ) * ((q : ℝ) + 1) := by
    have hd : (n : ℝ) = (m : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
    have hrR : (r : ℝ) ≤ m := by exact_mod_cast hr.le
    nlinarith
  have hquot : (n : ℝ) / m ≤ (q : ℝ) + 1 := (div_le_iff₀ hmp).mpr (by nlinarith)
  have hs := mul_le_mul_of_nonneg_left hquot hκ.le
  have hp := (hpow q).trans htailR
  have hid : κ / (m : ℝ) * n = κ * ((n : ℝ) / m) := by ring
  rw [hid]
  nlinarith

/-- Every infinite-order element in a group with a finite-index free subgroup is undistorted
for every finite semigroup-generating support. -/
theorem linear_word_growth_of_finiteIndex_free (H : Subgroup G) [H.FiniteIndex] [IsFreeGroup H]
    (s : Finset G) (hgen : Submonoid.closure (s : Set G) = ⊤) (g : G) (hg : ¬IsOfFinOrder g) :
    ∃ κ E : ℝ, 0 < κ ∧ 0 ≤ E ∧ ∀ n : ℕ,
      κ * n - E ≤ (wordDistance s hgen 1 (g ^ n) : ℝ) := by
  obtain ⟨m, hm, κ, hκ, hbound⟩ := exists_power_linear_word_growth_of_finiteIndex_free H s hgen g hg
  exact linear_word_growth_of_power s hgen g m hm κ hκ hbound

end Singularity
