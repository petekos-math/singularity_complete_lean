import Singularity.JumpDistance

/-!
# The symmetric word distance and its comparison with jump distance

Adjoin the inverses of the finite support and minimize permitted path length.
The resulting natural-valued distance is symmetric, separates points, is left
invariant, and satisfies the triangle inequality. The original directed jump
distance is uniformly comparable to this symmetric word distance.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Reversing a path in an inverse-closed support costs at most the same number of jumps. -/
theorem jumpDistance_reverse_word_bound (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (hinv : ∀ g ∈ s, g⁻¹ ∈ s)
    (n : ℕ) (w : WalkWord s n) (x : Γ) :
    jumpDistance s hgen (walkEndpoint s n x w) x ≤ n := by
  induction n generalizing x with
  | zero => exact Nat.le_of_eq ((jumpDistance_eq_zero_iff s hgen x x).mpr rfl)
  | succ n ih =>
    change jumpDistance s hgen (walkEndpoint s n (x * w.1) w.2) x ≤ n + 1
    have hstep : jumpDistance s hgen (x * w.1) x ≤ 1 := by
      simpa only [mul_inv_cancel_right] using
        jumpDistance_jump_le_one s hgen (x * w.1) (hinv w.1 w.1.property)
    exact (jumpDistance_triangle s hgen _ (x * w.1) x).trans (Nat.add_le_add (ih w.2 _) hstep)

/-- Inverse-closed supports have symmetric minimum jump distance. -/
theorem jumpDistance_symm_of_inverse_closed (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (hinv : ∀ g ∈ s, g⁻¹ ∈ s)
    (x y : Γ) : jumpDistance s hgen x y = jumpDistance s hgen y x := by
  have hle (x y : Γ) : jumpDistance s hgen y x ≤ jumpDistance s hgen x y := by
    obtain ⟨w, hw⟩ := jumpDistance_realized s hgen x y
    simpa only [hw] using jumpDistance_reverse_word_bound s hgen hinv _ w x
  exact Nat.le_antisymm (hle y x) (hle x y)

/-- The support together with its inverses. -/
def symmetricWordSupport (s : Finset Γ) : Finset Γ := s ∪ s.map ⟨Inv.inv, inv_injective⟩

theorem mem_symmetricWordSupport (s : Finset Γ) (g : Γ) :
    g ∈ symmetricWordSupport s ↔ g ∈ s ∨ g⁻¹ ∈ s := by
  rw [symmetricWordSupport, Finset.mem_union]
  apply or_congr_right
  constructor
  · intro hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
    simpa only [Function.Embedding.coeFn_mk, inv_inv] using ha
  · intro hg
    exact Finset.mem_map.mpr ⟨g⁻¹, hg, inv_inv g⟩

theorem symmetricWordSupport_inverse_closed (s : Finset Γ) (g : Γ)
    (hg : g ∈ symmetricWordSupport s) : g⁻¹ ∈ symmetricWordSupport s := by
  simpa only [mem_symmetricWordSupport, inv_inv, or_comm] using hg

theorem symmetricWordSupport_generates (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    Submonoid.closure (symmetricWordSupport s : Set Γ) = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact Submonoid.closure_mono (fun g hg => (mem_symmetricWordSupport s g).mpr (Or.inl hg))

/-- Minimum length for the symmetrized finite generating set. -/
def wordDistance (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) : ℕ :=
  jumpDistance (symmetricWordSupport s) (symmetricWordSupport_generates s hgen) x y

theorem wordDistance_eq_zero_iff (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x y : Γ) : wordDistance s hgen x y = 0 ↔ x = y :=
  jumpDistance_eq_zero_iff _ _ x y

theorem wordDistance_symm (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x y : Γ) : wordDistance s hgen x y = wordDistance s hgen y x :=
  jumpDistance_symm_of_inverse_closed _ _ (symmetricWordSupport_inverse_closed s) x y

theorem wordDistance_left (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (g x y : Γ) : wordDistance s hgen (g * x) (g * y) = wordDistance s hgen x y :=
  jumpDistance_left _ _ g x y

theorem wordDistance_triangle (s : Finset Γ) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (x y z : Γ) : wordDistance s hgen x z ≤ wordDistance s hgen x y + wordDistance s hgen y z :=
  jumpDistance_triangle _ _ x y z

/-- Adding inverse jumps cannot increase shortest-path length. -/
theorem wordDistance_le_jumpDistance (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) :
    wordDistance s hgen x y ≤ jumpDistance s hgen x y := by
  obtain ⟨w, hw⟩ := jumpDistance_realized s hgen x y
  have h := jumpDistance_word_bound (symmetricWordSupport s) (symmetricWordSupport_generates s hgen)
    s 1 (fun g hg => by
      simpa only [one_mul] using jumpDistance_jump_le_one (symmetricWordSupport s)
        (symmetricWordSupport_generates s hgen) 1 ((mem_symmetricWordSupport s g).mpr (Or.inl hg))) _ w x
  simpa only [wordDistance, hw, one_mul] using h

/-- Semigroup generation allows inverse jumps to be replaced uniformly by forward words. -/
theorem jumpDistance_le_wordDistance_mul (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    ∃ L : ℕ, 0 < L ∧ ∀ x y, jumpDistance s hgen x y ≤ L * wordDistance s hgen x y :=
  jumpDistance_comparison s (symmetricWordSupport s) hgen (symmetricWordSupport_generates s hgen)

end Singularity
