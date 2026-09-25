import Mathlib.GroupTheory.OrderOfElement

/-!
# Coordinates on a union of disjoint cyclic orbits

Infinite order and distinct orbit representatives yield a bijection ℤ × J → A.
The geometric assertion that a separator admits finitely many such orbits is
not asserted here.
-/

noncomputable section

namespace Singularity

variable {Γ J : Type*} [Group Γ]

/-- The union of the left cyclic orbits of the chosen representatives. -/
def cyclicOrbitUnion (a : Γ) (b : J → Γ) : Set Γ :=
  Set.range (fun p : ℤ × J => a ^ p.1 * b p.2)

/-- Representatives from distinct cyclic orbits give injective integer coordinates. -/
theorem cyclicOrbit_injective (a : Γ) (b : J → Γ) (ha : ¬IsOfFinOrder a)
    (hb : ∀ j k (n : ℤ), a ^ n * b j = b k → j = k) :
    Function.Injective (fun p : ℤ × J => a ^ p.1 * b p.2) := by
  rintro ⟨n, j⟩ ⟨m, k⟩ h
  have hj : j = k := by
    apply hb j k (n - m)
    calc
      a ^ (n - m) * b j = a ^ (-m) * (a ^ n * b j) := by
        rw [← mul_assoc, ← zpow_add]
        congr 2
        omega
      _ = a ^ (-m) * (a ^ m * b k) := congrArg (fun z => a ^ (-m) * z) h
      _ = b k := by rw [← mul_assoc, ← zpow_add]; simp
  subst k
  have hn : n = m := injective_zpow_iff_not_isOfFinOrder.mpr ha (mul_right_cancel h)
  subst m
  rfl

/-- A concrete orbit enumeration, rather than an assumed Hilbert-space identification. -/
def cyclicOrbitEquiv (a : Γ) (b : J → Γ) (ha : ¬IsOfFinOrder a)
    (hb : ∀ j k (n : ℤ), a ^ n * b j = b k → j = k) : (ℤ × J) ≃ cyclicOrbitUnion a b :=
  Equiv.ofBijective
    (fun p => ⟨a ^ p.1 * b p.2, ⟨p, rfl⟩⟩)
    ⟨fun p q h => cyclicOrbit_injective a b ha hb (congrArg Subtype.val h), by
      rintro ⟨x, p, hp⟩
      exact ⟨p, Subtype.ext hp⟩⟩

theorem cyclicOrbitEquiv_apply (a : Γ) (b : J → Γ) (ha : ¬IsOfFinOrder a)
    (hb : ∀ j k (n : ℤ), a ^ n * b j = b k → j = k) (p : ℤ × J) :
    (cyclicOrbitEquiv a b ha hb p : Γ) = a ^ p.1 * b p.2 := rfl

/-- Multiplication by a cyclic power is integer translation of the orbit coordinate. -/
theorem cyclicOrbitEquiv_shift (a : Γ) (b : J → Γ) (ha : ¬IsOfFinOrder a)
    (hb : ∀ j k (n : ℤ), a ^ n * b j = b k → j = k) (m n : ℤ) (j : J) :
    a ^ m * (cyclicOrbitEquiv a b ha hb (n, j) : Γ) =
      (cyclicOrbitEquiv a b ha hb (m + n, j) : Γ) := by
  simp only [cyclicOrbitEquiv_apply, zpow_add, mul_assoc]

end Singularity
