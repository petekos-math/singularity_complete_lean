import Singularity.CoordinateBarrier

/-!
# The length of an excursion to a coordinate sublevel

If a walk visits the sublevel h ≤ r, it must spend at least
(h(x)+h(y)-2r)/L jumps travelling from x to that level and back to y.
We prove the contrapositive directly for permitted finite words, then identify
the unrestricted and killed transition weights below this cutoff.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- A coordinate with jump changes at most L changes by at most nL along a word. -/
theorem walkEndpoint_coordinate_bound (s : Finset Γ) (h : Γ → ℝ) (L : ℝ)
    (hjump : ∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L)
    (n : ℕ) (x : Γ) (w : WalkWord s n) :
    |h (walkEndpoint s n x w) - h x| ≤ (n : ℝ) * L := by
  induction n generalizing x with
  | zero => simp [walkEndpoint]
  | succ n ih =>
    rcases w with ⟨g,w⟩
    have h₁ := ih (x*g) w
    have h₂ := hjump x g g.property
    have ht := abs_add_le (h (walkEndpoint s n (x*g) w) - h (x*g)) (h (x*g) - h x)
    simp only [sub_add_sub_cancel] at ht
    change |h (walkEndpoint s n (x*g) w) - h x| ≤ _
    push_cast
    linarith

/-- A path shorter than the round trip to a sublevel avoids that sublevel
at every position, including its final point. -/
theorem walk_avoids_sublevel_of_short_excursion (s : Finset Γ) (h : Γ → ℝ) (L r : ℝ)
    (hjump : ∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L)
    (A : Set Γ) (hA : ∀ a ∈ A, h a ≤ r) (n : ℕ) (x : Γ) (w : WalkWord s n)
    (hshort : (n : ℝ) * L < h x + h (walkEndpoint s n x w) - 2*r) :
    avoidsBefore s A n x w ∧ walkEndpoint s n x w ∉ A := by
  induction n generalizing x with
  | zero =>
    refine ⟨trivial, ?_⟩
    intro hx
    have hh := hA x hx
    simp only [walkEndpoint, Nat.cast_zero, zero_mul] at hshort
    linarith
  | succ n ih =>
    rcases w with ⟨g,w⟩
    have hb := abs_le.mp (walkEndpoint_coordinate_bound s h L hjump (n+1) x (g,w))
    have hx : x ∉ A := by
      intro hx
      have hh := hA x hx
      linarith [hb.2]
    have hstep := (abs_le.mp (hjump x g g.property)).1
    have hs : (n : ℝ) * L < h (x*g) + h (walkEndpoint s n (x*g) w) - 2*r := by
      change ((n+1 : ℕ) : ℝ) * L < h x + h (walkEndpoint s n (x*g) w) - 2*r at hshort
      push_cast at hshort
      linarith
    have hn := ih (x*g) w hs
    exact ⟨⟨hx, hn.1⟩, hn.2⟩

/-- Below the excursion cutoff, killing removes none of the transition mass. -/
theorem killedWeight_eq_transition_of_short_excursion
    (s : Finset Γ) (μ : Γ → ℝ) (h : Γ → ℝ) (L r : ℝ)
    (hjump : ∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L)
    (A : Set Γ) (hA : ∀ a ∈ A, h a ≤ r) (n : ℕ) (x y : Γ)
    (hshort : (n : ℝ) * L < h x + h y - 2*r) :
    killedWeight s μ A n x y = transitionWeight s μ n x y := by
  unfold killedWeight transitionWeight
  apply Finset.sum_congr rfl
  intro w _
  by_cases he : walkEndpoint s n x w = y
  · have hh := walk_avoids_sublevel_of_short_excursion s h L r hjump A hA n x w
      (by simpa only [he] using hshort)
    have hy : y ∉ A := he ▸ hh.2
    simp only [hh.1, he, hy, not_false_eq_true, true_and, ite_true]
  · simp only [he, false_and, and_false, ite_false]

end Singularity
