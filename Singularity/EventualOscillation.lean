import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A uniform eventual comparison forces zero oscillation

The comparison may start at an index depending on the evaluation point.
Only its positive coefficient must be uniform. No uniform starting index or
convergence of the sampled values is assumed.
-/

noncomputable section
open Set Filter

namespace Singularity

/-- Simultaneous lower and upper comparisons along one sequence force a bounded
real function to be constant. -/
theorem constant_of_eventual_oscillation_comparison {X : Type*} [Nonempty X]
    (r : X → ℝ) (y : ℕ → X) (c : ℝ) (hc : 0 < c)
    (hbelow : BddBelow (range r)) (habove : BddAbove (range r))
    (hlower : ∀ x, ∀ᶠ n in atTop,
      c * (r (y n) - sInf (range r)) ≤ r x - sInf (range r))
    (hupper : ∀ x, ∀ᶠ n in atTop,
      c * (sSup (range r) - r (y n)) ≤ sSup (range r) - r x) :
    ∀ x z, r x = r z := by
  have hne : (range r).Nonempty := range_nonempty r
  have hlo (x : X) : sInf (range r) ≤ r x := csInf_le hbelow (mem_range_self x)
  have hhi (x : X) : r x ≤ sSup (range r) := le_csSup habove (mem_range_self x)
  have hwidth : sSup (range r) ≤ sInf (range r) := by
    by_contra h
    have hw : 0 < sSup (range r) - sInf (range r) := sub_pos.mpr (lt_of_not_ge h)
    let ε := c * (sSup (range r) - sInf (range r)) / 4
    have hε : 0 < ε := div_pos (mul_pos hc hw) (by norm_num)
    obtain ⟨a, ⟨x, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hne
      (show sInf (range r) < sInf (range r) + ε by linarith)
    obtain ⟨b, ⟨z, rfl⟩, hz⟩ := exists_lt_of_lt_csSup hne
      (show sSup (range r) - ε < sSup (range r) by linarith)
    obtain ⟨n, hn⟩ := ((hlower x).and (hupper z)).exists
    have hh := add_le_add hn.1 hn.2
    dsimp only [ε] at hx hz
    nlinarith
  intro x z
  exact le_antisymm ((hhi x).trans (hwidth.trans (hlo z)))
    ((hhi z).trans (hwidth.trans (hlo x)))

end Singularity
