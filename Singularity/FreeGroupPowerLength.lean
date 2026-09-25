import Singularity.WordDistance
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Linear growth of powers in a free group

Mathlib's cyclic reduction formula gives the exact reduced-word length of
positive powers. A nonidentity word has a nonempty cyclic core, so the length
of its nth power is at least n. This includes commutators and does not use
nonzero abelianization.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {α : Type*}

/-- A nonidentity reduced word has a nonempty cyclic reduction. -/
theorem freeGroup_cyclic_core_ne_nil (g : FreeGroup α) (hg : g ≠ 1) :
    FreeGroup.reduceCyclically g.toWord ≠ [] := by
  intro he
  have h := congrArg FreeGroup.mk (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically g.toWord)
  rw [he, List.append_nil, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, mul_inv_cancel,
    FreeGroup.mk_toWord] at h
  exact hg h.symm

/-- The exact positive-power length consists of the conjugator and repeated cyclic core. -/
theorem freeGroup_norm_pow_succ (g : FreeGroup α) (n : ℕ) :
    FreeGroup.norm (g ^ (n + 1)) =
      2 * (FreeGroup.reduceCyclically.conjugator g.toWord).length +
        (n + 1) * (FreeGroup.reduceCyclically g.toWord).length := by
  rw [FreeGroup.norm, FreeGroup.toWord_pow,
    FreeGroup.reduceCyclically.reduce_flatten_replicate_succ FreeGroup.isReduced_toWord]
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul, FreeGroup.invRev_length]
  omega

/-- Every nonidentity free-group element has at least linear reduced-word growth. -/
theorem freeGroup_norm_pow_ge (g : FreeGroup α) (hg : g ≠ 1) (n : ℕ) :
    n ≤ FreeGroup.norm (g ^ n) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    rw [freeGroup_norm_pow_succ]
    have hc : 1 ≤ (FreeGroup.reduceCyclically g.toWord).length :=
      List.length_pos_iff.mpr (freeGroup_cyclic_core_ne_nil g hg)
    have h := Nat.mul_le_mul_left (n + 1) hc
    omega

end Singularity
