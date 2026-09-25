import Singularity.WalkKernel
import Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Reachability and strict positivity of the Green kernel

The support must generate as a semigroup (equivalently here, as a submonoid),
and every listed jump has strictly positive weight. Group generation alone is
not used as a substitute for this hypothesis. Green convergence still uses the
operator spectral-gap hypothesis.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Every element in the generated submonoid is the endpoint of a finite jump word. -/
theorem exists_walkWord_of_mem_closure (s : Finset Γ) {g : Γ}
    (hg : g ∈ Submonoid.closure (s : Set Γ)) :
    ∃ (n : ℕ) (w : WalkWord s n), walkEndpoint s n 1 w = g := by
  induction hg using Submonoid.closure_induction_left with
  | one => exact ⟨0, PUnit.unit, rfl⟩
  | mul_left a ha b _ ih =>
    obtain ⟨n, w, hw⟩ := ih
    refine ⟨n + 1, (⟨a, ha⟩, w), ?_⟩
    change walkEndpoint s n (1 * a) w = a * b
    rw [one_mul, ← mul_one a, walkEndpoint_left, hw, mul_one]

/-- Semigroup generation gives a permitted finite path between every pair of states. -/
theorem exists_walkWord_between (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) :
    ∃ (n : ℕ) (w : WalkWord s n), walkEndpoint s n x w = y := by
  have hg : x⁻¹ * y ∈ Submonoid.closure (s : Set Γ) := by rw [hgen]; trivial
  obtain ⟨n, w, hw⟩ := exists_walkWord_of_mem_closure s hg
  refine ⟨n, w, ?_⟩
  rw [← mul_one x, walkEndpoint_left, hw, mul_inv_cancel_left]

omit [Group Γ] in
/-- A finite word of strictly positive-weight jumps has strictly positive weight. -/
theorem walkWeight_pos (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (n : ℕ) (w : WalkWord s n) :
    0 < walkWeight s μ n w := by
  induction n with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (hμ w.1 w.1.property) (ih w.2)

/-- The weight of any permitted path is bounded by the transition coefficient it contributes to. -/
theorem walkWeight_le_transition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (n : ℕ) (w : WalkWord s n) (x : Γ) :
    walkWeight s μ n w ≤ transitionWeight s μ n x (walkEndpoint s n x w) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun v : WalkWord s n => if walkEndpoint s n x v = walkEndpoint s n x w
      then walkWeight s μ n v else 0)
    (fun v _ => by split_ifs; exact walkWeight_nonneg s μ hμ n v; exact le_rfl)
    (Finset.mem_univ w)
  simpa only [ite_true, transitionWeight] using h

/-- Any positive path gives a positive transition coefficient. -/
theorem transitionWeight_pos_of_path (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (n : ℕ) (w : WalkWord s n) (x y : Γ)
    (hw : walkEndpoint s n x w = y) : 0 < transitionWeight s μ n x y := by
  subst y
  exact (walkWeight_pos s μ hμ n w).trans_le
    (walkWeight_le_transition s μ (fun g hg => (hμ g hg).le) n w x)

/-- The finite-step transition kernel is irreducible under semigroup generation. -/
theorem exists_transitionWeight_pos (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (x y : Γ) :
    ∃ n, 0 < transitionWeight s μ n x y := by
  obtain ⟨n, w, hw⟩ := exists_walkWord_between s hgen x y
  exact ⟨n, transitionWeight_pos_of_path s μ hμ n w x y hw⟩

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]

/-- A positive transition coefficient gives a strictly positive convergent Green entry. -/
theorem walkGreen_pos_of_transition (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (x y : Γ) {n : ℕ} (hn : 0 < transitionWeight s μ n x y) : 0 < walkGreen s μ x y :=
  hn.trans_le ((walkGreen_summable s μ hgap x y).le_tsum n
    (fun k _ => transitionWeight_nonneg s μ hμ k x y))

/-- Every Green entry is positive under the actual semigroup-generation hypothesis. -/
theorem walkGreen_pos (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) : 0 < walkGreen s μ x y := by
  obtain ⟨n, hn⟩ := exists_transitionWeight_pos s μ hμ hgen x y
  exact walkGreen_pos_of_transition s μ (fun g hg => (hμ g hg).le) hgap x y hn

/-- In particular the canonical Green normalizers never vanish. -/
theorem walkGreen_ne_zero (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x y : Γ) : walkGreen s μ x y ≠ 0 :=
  ne_of_gt (walkGreen_pos s μ hμ hgen hgap x y)

end Singularity
