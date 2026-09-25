import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Common subtraction and contraction of normalized functions

Successive normalized kernels remove the same function from two initially
normalized inputs. If each removal captures a fixed fraction and preserves
nonnegativity on nested domains, the difference decays geometrically. This
proves the algebraic iteration; the domain boundary-Harnack comparisons that
supply the removal bounds remain separate geometric obligations.
-/

noncomputable section
namespace Singularity

/-- Successively subtract a normalized kernel scaled by the current base value. -/
def commonSubtraction {X : Type*} (k : ℕ → X → ℝ) (c : ℝ) (o : X) (f : X → ℝ) : ℕ → X → ℝ
  | 0 => f
  | n+1 => fun x => commonSubtraction k c o f n x - c * commonSubtraction k c o f n o * k n x

/-- The values at the normalization point follow a scalar geometric schedule. -/
theorem commonSubtraction_base {X : Type*} (k : ℕ → X → ℝ) (c : ℝ) (o : X) (f : X → ℝ)
    (hk : ∀ n, k n o = 1) (n : ℕ) :
    commonSubtraction k c o f n o = (1-c)^n * f o := by
  induction n with
  | zero => simp [commonSubtraction]
  | succ n ih => simp only [commonSubtraction, hk, mul_one, ih, pow_succ]; ring

/-- Equal initial normalization makes all the removed terms identical. -/
theorem commonSubtraction_difference {X : Type*} (k : ℕ → X → ℝ) (c : ℝ) (o : X) (f g : X → ℝ)
    (hk : ∀ n, k n o = 1) (hfg : f o = g o) (n : ℕ) (x : X) :
    commonSubtraction k c o f n x - commonSubtraction k c o g n x = f x - g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hb : commonSubtraction k c o f n o = commonSubtraction k c o g n o := by
      rw [commonSubtraction_base k c o f hk, commonSubtraction_base k c o g hk, hfg]
    simp only [commonSubtraction, hb]
    linear_combination ih

/-- Local fractional removal on nested domains gives a geometric upper bound. -/
theorem commonSubtraction_geometric_bound {X : Type*} (k : ℕ → X → ℝ) (c ε : ℝ) (o : X)
    (f : X → ℝ) (S : ℕ → Set X) (N : ℕ) (_hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hS : ∀ n < N, S (n+1) ⊆ S n) (hf : ∀ x ∈ S 0, 0 ≤ f x)
    (hremove : ∀ n < N, ∀ x ∈ S (n+1),
      ε * commonSubtraction k c o f n x ≤ c * commonSubtraction k c o f n o * k n x ∧
      c * commonSubtraction k c o f n o * k n x ≤ commonSubtraction k c o f n x) :
    ∀ n ≤ N, ∀ x ∈ S n, 0 ≤ commonSubtraction k c o f n x ∧
      commonSubtraction k c o f n x ≤ (1-ε)^n * f x := by
  intro n
  induction n with
  | zero => intro _ x hx; simpa only [commonSubtraction, pow_zero, one_mul] using And.intro (hf x hx) le_rfl
  | succ n ih =>
    intro hn x hx
    have hnN : n < N := by omega
    obtain ⟨hpos, hbound⟩ := ih (by omega) x (hS n hnN hx)
    obtain ⟨hlo, hhi⟩ := hremove n hnN x hx
    change 0 ≤ commonSubtraction k c o f n x - c * commonSubtraction k c o f n o * k n x ∧ _
    refine ⟨by linarith, ?_⟩
    change commonSubtraction k c o f n x - c * commonSubtraction k c o f n o * k n x ≤ _
    calc
      _ ≤ (1-ε) * commonSubtraction k c o f n x := by linarith
      _ ≤ (1-ε) * ((1-ε)^n * f x) := mul_le_mul_of_nonneg_left hbound (by linarith)
      _ = _ := by rw [pow_succ]; ring

/-- Two equally normalized functions become exponentially close when their
common subtraction is admissible on the same nested domains. -/
theorem commonSubtraction_contraction {X : Type*} (k : ℕ → X → ℝ) (c ε : ℝ) (o : X)
    (f g : X → ℝ) (S : ℕ → Set X) (N : ℕ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hk : ∀ n, k n o = 1) (hfg : f o = g o)
    (hS : ∀ n < N, S (n+1) ⊆ S n) (hf : ∀ x ∈ S 0, 0 ≤ f x) (hg : ∀ x ∈ S 0, 0 ≤ g x)
    (hremove : ∀ u ∈ ({f,g} : Set (X → ℝ)), ∀ n < N, ∀ x ∈ S (n+1),
      ε * commonSubtraction k c o u n x ≤ c * commonSubtraction k c o u n o * k n x ∧
      c * commonSubtraction k c o u n o * k n x ≤ commonSubtraction k c o u n x) :
    ∀ x ∈ S N, |f x - g x| ≤ (1-ε)^N * (f x + g x) := by
  intro x hx
  have hfb := commonSubtraction_geometric_bound k c ε o f S N hε hε1 hS hf
    (hremove f (by simp)) N le_rfl x hx
  have hgb := commonSubtraction_geometric_bound k c ε o g S N hε hε1 hS hg
    (hremove g (by simp)) N le_rfl x hx
  rw [← commonSubtraction_difference k c o f g hk hfg N x]
  apply abs_le.mpr
  constructor <;> nlinarith [hfb.1, hfb.2, hgb.1, hgb.2]

/-- A two-sided boundary Harnack comparison supplies an admissible common
removal: c=1/C removes at least the fraction ε=1/C². -/
theorem fractional_removal_of_comparison (C u b k : ℝ) (hC : 0 < C)
    (hlo : b*k/C ≤ u) (hhi : u ≤ C*(b*k)) :
    (1/C^2)*u ≤ (1/C)*b*k ∧ (1/C)*b*k ≤ u := by
  have hh := div_le_div_of_nonneg_right hhi (sq_nonneg C)
  have he : C*(b*k)/C^2 = (1/C)*b*k := by field_simp
  constructor
  · rw [he] at hh
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh
  · convert hlo using 1
    ring

end Singularity
