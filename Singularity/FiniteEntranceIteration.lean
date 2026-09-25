import Singularity.EntrancePairTransfer
import Singularity.LocalTransferIteration
import Singularity.HyperbolicHarnack
import Singularity.ReflectedSupport

/-!
# A finite first/last-entry iteration for the actual Green kernel

All transfer maps are the actual first-entry or reflected last-entry kernels.
The local admissible pair sets track precisely where each detour estimate is
required. Small total discarded mass and a terminal product comparison give a
uniform product comparison at the initial pairs. The later CocompactAxisAncona
module constructs a geometric sequence satisfying those conditions.
-/

noncomputable section
open scoped Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- Actual first/last-entry transfers give a factor-two product estimate once
their local relative errors sum to at most one half. -/
theorem finite_entrance_iteration_bound {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (N : ℕ) (A : ℕ → Finset Γ) (last : ℕ → Bool) (S : ℕ → Set (Γ × Γ)) (ε : ℕ → ℝ)
    (o : Γ) (C : ℝ) (hC : 0 ≤ C)
    (hε : ∀ n < N, 0 ≤ ε n) (hsum : ∑ n ∈ Finset.range N, ε n ≤ 1 / 2)
    (hmove : ∀ n < N, ∀ p ∈ S n, ∀ a : A n,
      (if last n then (p.1, (a : Γ)) else ((a : Γ), p.2)) ∈ S (n + 1))
    (herror : ∀ n < N, ∀ p ∈ S n,
      entrancePairRemainder s μ (A n) (last n) p ≤ ε n * walkGreen s μ p.1 p.2)
    (hterminal : ∀ p ∈ S N,
      walkGreen s μ p.1 p.2 ≤ C * (walkGreen s μ p.1 o * walkGreen s μ o p.2)) :
    ∀ p ∈ S 0, walkGreen s μ p.1 p.2 ≤
      2 * C * (walkGreen s μ p.1 o * walkGreen s μ o p.2) := by
  apply local_transfer_half_error_bound N (fun n => entrancePairTransfer s μ (A n) (last n))
    S ε (fun p => walkGreen s μ p.1 p.2)
    (fun p => walkGreen s μ p.1 o * walkGreen s μ o p.2) C hC
    (fun p => walkGreen_nonneg s μ hμ p.1 p.2) hε hsum
  · intro n hn f g hh
    exact entrancePairTransfer_monoOn s μ hμ (A n) (last n) (S n) (S (n + 1))
      (hmove n hn) f g hh
  · intro n _ p _
    exact entrancePairTransfer_product_le s μ hμ hmass hgap (A n) (last n) o p
  · intro n hn p hp
    have he := entrancePairTransfer_green_decomposition s μ hμ hmass hgap (A n) (last n) p
    have hh := herror n hn p hp
    linarith
  · exact hterminal

/-- The terminal comparison is automatic when the left endpoint is within
a fixed hyperbolic distance of the center; its constant is uniform in the right endpoint. -/
theorem hyperbolic_near_center_green_product_bound (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x o y : Γ,
      dist (x • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ R →
      walkGreen s μ x y ≤ C * (walkGreen s μ x o * walkGreen s μ o y) := by
  obtain ⟨c, hc, hh⟩ := hyperbolic_uniform_greenHarnack Γ s μ hpos hgen hgap R
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  refine ⟨c ^ 2, sq_pos_of_pos hc0, ?_⟩
  intro x o y hxo
  have hleft := hh o x y (by simpa only [dist_comm] using hxo)
  have hright := (walkGreen_diag_ge_one s μ hμ hgap o).trans (hh x o o hxo)
  calc
    _ ≤ c * walkGreen s μ o y := hleft
    _ ≤ (c * walkGreen s μ x o) * (c * walkGreen s μ o y) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hright
        (mul_nonneg hc0.le (walkGreen_nonneg s μ hμ o y))
    _ = _ := by ring

/-- With terminal pairs near the center, only the geometric reachability and
detour-error conditions remain to obtain a uniform comparison. -/
theorem hyperbolic_finite_entrance_iteration (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (R : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ) (A : ℕ → Finset Γ) (last : ℕ → Bool)
      (S : ℕ → Set (Γ × Γ)) (ε : ℕ → ℝ) (o : Γ),
      (∀ n < N, 0 ≤ ε n) → (∑ n ∈ Finset.range N, ε n ≤ 1 / 2) →
      (∀ n < N, ∀ p ∈ S n, ∀ a : A n,
        (if last n then (p.1, (a : Γ)) else ((a : Γ), p.2)) ∈ S (n + 1)) →
      (∀ n < N, ∀ p ∈ S n,
        entrancePairRemainder s μ (A n) (last n) p ≤ ε n * walkGreen s μ p.1 p.2) →
      (∀ p ∈ S N, dist (p.1 • UpperHalfPlane.I) (o • UpperHalfPlane.I) ≤ R) →
      ∀ p ∈ S 0, walkGreen s μ p.1 p.2 ≤ H * (walkGreen s μ p.1 o * walkGreen s μ o p.2) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  obtain ⟨C, hC, hterminal⟩ := hyperbolic_near_center_green_product_bound Γ s μ hpos hgen hgap R
  refine ⟨2 * C, by positivity, ?_⟩
  intro N A last S ε o hε hsum hmove herror hclose
  exact finite_entrance_iteration_bound s μ (fun g hg => (hpos g hg).le) hmass hgap
    N A last S ε o C hC.le hε hsum hmove herror
    (fun p hp => hterminal p.1 o p.2 (hclose p hp))

end Singularity
