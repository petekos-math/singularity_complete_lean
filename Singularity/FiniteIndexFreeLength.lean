import Singularity.SchreierRetraction
import Singularity.FreeGroupPowerLength
import Mathlib.GroupTheory.Schreier

/-!
# Word-length lower bounds from a finite-index free subgroup

There are finitely many Schreier transitions for a finite support and a
finite-index subgroup. Their free-word lengths bound the norm of every subgroup
element by its ambient word length. Cyclic reduction then gives linear ambient
word growth for each nonidentity element of the free subgroup. Every
infinite-order ambient element has a positive power in that subgroup.
-/

noncomputable section
open Set Subgroup
open scoped Classical

namespace Singularity

variable {G α : Type*} [Group G]

/-- A homomorphism from a finite-index subgroup to a free group has a uniform
free-word norm bound in terms of the ambient finite-support word distance. -/
theorem finiteIndex_free_norm_word_bound (H : Subgroup G) [H.FiniteIndex]
    (φ : H →* FreeGroup α) (s : Finset G) (hgen : Submonoid.closure (s : Set G) = ⊤) :
    ∃ L : ℕ, 0 < L ∧ ∀ h : H, FreeGroup.norm (φ h) ≤ L * wordDistance s hgen 1 (h : G) := by
  obtain ⟨R, hR, hR1⟩ := H.exists_isComplement_right 1
  let : Finite R := hR.finite_right_iff.mpr inferInstance
  let : Fintype R := Fintype.ofFinite R
  let t := symmetricWordSupport s
  let L := 1 + ∑ r : R, ∑ g : t,
    FreeGroup.norm (φ (schreierRetraction H R hR ((r : G) * (g : G))))
  have hL (r : R) (g : G) (hg : g ∈ t) :
      FreeGroup.norm (φ (schreierRetraction H R hR ((r : G) * g))) ≤ L := by
    have h₁ := Finset.single_le_sum (s := Finset.univ)
      (f := fun a : t => FreeGroup.norm (φ (schreierRetraction H R hR ((r : G) * (a : G)))))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨g, hg⟩ : t))
    have h₂ := Finset.single_le_sum (s := Finset.univ)
      (f := fun r : R => ∑ a : t, FreeGroup.norm (φ (schreierRetraction H R hR ((r : G) * (a : G)))))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    exact (h₁.trans h₂).trans (by dsimp [L]; omega)
  refine ⟨L, by dsimp [L]; omega, fun h => ?_⟩
  obtain ⟨w, hw⟩ := jumpDistance_realized t (symmetricWordSupport_generates s hgen) 1 (h : G)
  have hb := schreierRetraction_word_norm H R hR φ t L hL _ w 1
  rw [hw, schreierRetraction_subgroup H R hR hR1 h] at hb
  have hret : schreierRetraction H R hR (1 : G) = 1 :=
    schreierRetraction_subgroup H R hR hR1 1
  simpa only [hret, map_one, FreeGroup.norm_one, Nat.zero_add, wordDistance] using hb

/-- Every nonidentity element of a finite-index free subgroup has linear
word growth measured in the original ambient generating set. -/
theorem finiteIndex_free_power_word_lower (H : Subgroup G) [H.FiniteIndex] [IsFreeGroup H]
    (s : Finset G) (hgen : Submonoid.closure (s : Set G) = ⊤) (h : H) (hh : h ≠ 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ, κ * n ≤ (wordDistance s hgen 1 ((h : G) ^ n) : ℝ) := by
  let φ := (IsFreeGroup.toFreeGroup H).toMonoidHom
  obtain ⟨L, hL, hbound⟩ := finiteIndex_free_norm_word_bound H φ s hgen
  have hφ : φ h ≠ 1 := by
    intro he
    apply hh
    apply (IsFreeGroup.toFreeGroup H).injective
    simpa [φ] using he
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨(L : ℝ)⁻¹, inv_pos.mpr hLp, fun n => ?_⟩
  have hnorm := freeGroup_norm_pow_ge (φ h) hφ n
  have hb := hbound (h ^ n)
  rw [map_pow] at hb
  have hr : (n : ℝ) ≤ (L : ℝ) * (wordDistance s hgen 1 ((h : G) ^ n) : ℝ) := by
    exact_mod_cast hnorm.trans hb
  have hd : (n : ℝ) / (L : ℝ) ≤ (wordDistance s hgen 1 ((h : G) ^ n) : ℝ) :=
    (div_le_iff₀ hLp).mpr (by simpa only [mul_comm] using hr)
  simpa only [div_eq_mul_inv, mul_comm] using hd

/-- An infinite-order element has a positive power with linear word growth
whenever the ambient group has a finite-index free subgroup. -/
theorem exists_power_linear_word_growth_of_finiteIndex_free (H : Subgroup G)
    [H.FiniteIndex] [IsFreeGroup H]
    (s : Finset G) (hgen : Submonoid.closure (s : Set G) = ⊤)
    (g : G) (hg : ¬IsOfFinOrder g) :
    ∃ m : ℕ, 0 < m ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ,
      κ * n ≤ (wordDistance s hgen 1 ((g ^ m) ^ n) : ℝ) := by
  obtain ⟨m, hm, _, hmem⟩ := H.exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero g
  let h : H := ⟨g ^ m, hmem⟩
  have hh : h ≠ 1 := by
    intro he
    apply hg
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, congrArg Subtype.val he⟩
  obtain ⟨κ, hκ, hbound⟩ := finiteIndex_free_power_word_lower H s hgen h hh
  exact ⟨m, hm, κ, hκ, hbound⟩

end Singularity
