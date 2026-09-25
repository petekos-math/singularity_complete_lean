import Singularity.WordDistance

/-!
# Shortest word paths and their subpaths

Shortest words give chains of group vertices. Every subchain is again shortest;
for the symmetric word distance the distance between its vertices is exactly
the difference of their indices.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- A permitted finite word can be displayed as a chain of vertices. -/
theorem walkWord_vertex_chain (s : Finset Γ) (n : ℕ) (w : WalkWord s n) (x : Γ) :
    ∃ p : ℕ → Γ, p 0 = x ∧ p n = walkEndpoint s n x w ∧
      ∀ k < n, ∃ g ∈ s, p (k + 1) = p k * g := by
  induction n generalizing x with
  | zero => exact ⟨fun _ => x, rfl, rfl, by omega⟩
  | succ n ih =>
    obtain ⟨q, hq0, hqn, hstep⟩ := ih w.2 (x * w.1)
    let p : ℕ → Γ := fun k => if k = 0 then x else q (k - 1)
    refine ⟨p, by simp [p], ?_, ?_⟩
    · simpa only [p, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, walkEndpoint] using hqn
    · intro k hk
      rcases k with _ | k
      · exact ⟨w.1, w.1.property, by simpa [p] using hq0⟩
      · simpa only [p, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] using hstep k (by omega)

/-- Any subchain bounds the directed distance by its number of steps. -/
theorem jumpDistance_chain_le (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (p : ℕ → Γ) (N : ℕ)
    (hstep : ∀ k < N, ∃ g ∈ s, p (k + 1) = p k * g)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ N) :
    jumpDistance s hgen (p i) (p j) ≤ j - i := by
  suffices h : ∀ d, i + d ≤ N → jumpDistance s hgen (p i) (p (i + d)) ≤ d by
    simpa only [Nat.add_sub_of_le hij] using h (j - i) (by omega)
  intro d
  induction d with
  | zero => intro _; simp only [Nat.add_zero, (jumpDistance_eq_zero_iff s hgen _ _).mpr rfl, le_refl]
  | succ d ih =>
    intro hd
    obtain ⟨g, hg, he⟩ := hstep (i + d) (by omega)
    have hnext : jumpDistance s hgen (p (i + d)) (p (i + (d + 1))) ≤ 1 := by
      rw [show i + (d + 1) = (i + d) + 1 by omega, he]
      exact jumpDistance_jump_le_one s hgen _ hg
    exact (jumpDistance_triangle s hgen _ (p (i + d)) _).trans
      (Nat.add_le_add (ih (by omega)) hnext)

/-- Every forward subchain of a shortest directed path is shortest. -/
theorem jumpDistance_shortest_chain (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (p : ℕ → Γ) (N : ℕ)
    (hstep : ∀ k < N, ∃ g ∈ s, p (k + 1) = p k * g)
    (hshort : jumpDistance s hgen (p 0) (p N) = N)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ N) :
    jumpDistance s hgen (p i) (p j) = j - i := by
  have hprefix := jumpDistance_chain_le s hgen p N hstep 0 i (Nat.zero_le _) (by omega)
  have hmiddle := jumpDistance_chain_le s hgen p N hstep i j hij hj
  have hsuffix := jumpDistance_chain_le s hgen p N hstep j N hj (le_refl _)
  have ht1 := jumpDistance_triangle s hgen (p 0) (p i) (p N)
  have ht2 := jumpDistance_triangle s hgen (p i) (p j) (p N)
  omega

/-- A shortest symmetric word path has exactly the index distance between
every pair of vertices, and every step is an original or inverse generator. -/
theorem wordDistance_geodesic_chain (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) :
    ∃ p : ℕ → Γ, p 0 = x ∧ p (wordDistance s hgen x y) = y ∧
      (∀ k < wordDistance s hgen x y,
        ∃ g ∈ symmetricWordSupport s, p (k + 1) = p k * g) ∧
      (∀ i ≤ wordDistance s hgen x y, ∀ j ≤ wordDistance s hgen x y,
        (wordDistance s hgen (p i) (p j) : ℝ) = |(i : ℝ) - (j : ℝ)|) := by
  obtain ⟨w, hw⟩ := jumpDistance_realized (symmetricWordSupport s)
    (symmetricWordSupport_generates s hgen) x y
  obtain ⟨p, hp0, hpN, hstep⟩ := walkWord_vertex_chain (symmetricWordSupport s) _ w x
  have hend : p (wordDistance s hgen x y) = y := hpN.trans hw
  have hshort : jumpDistance (symmetricWordSupport s) (symmetricWordSupport_generates s hgen)
      (p 0) (p (wordDistance s hgen x y)) = wordDistance s hgen x y := by rw [hp0, hend]; rfl
  refine ⟨p, hp0, hend, hstep, ?_⟩
  intro i hi j hj
  rcases le_total i j with hij | hji
  · have he := jumpDistance_shortest_chain _ _ p _ hstep hshort i j hij hj
    change (jumpDistance (symmetricWordSupport s) (symmetricWordSupport_generates s hgen) (p i) (p j) : ℝ) = _
    rw [he, Nat.cast_sub hij, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hij))]
    ring
  · rw [wordDistance_symm]
    have he := jumpDistance_shortest_chain _ _ p _ hstep hshort j i hji hi
    change (jumpDistance (symmetricWordSupport s) (symmetricWordSupport_generates s hgen) (p j) (p i) : ℝ) = _
    rw [he, Nat.cast_sub hji, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hji))]

end Singularity
