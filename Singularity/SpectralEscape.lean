import Singularity.InfiniteWalkProcess

/-!
# Spectral decay and escape from small finite sets

Operator spectral decay bounds transition probabilities uniformly. A family of
finite sets whose cardinalities grow slowly enough therefore has summable visit
probabilities; Borel--Cantelli gives eventual avoidance on the actual path space.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ]

/-- Transition probabilities are bounded by the operator norm of the corresponding power. -/
theorem transitionWeight_le_power_norm (s : Finset Γ) (μ : Γ → ℝ)
    (n : ℕ) (x y : Γ) : transitionWeight s μ n x y ≤ ‖rightMarkov s μ ^ n‖ := by
  have h := (countingEvaluation_le x ((rightMarkov s μ ^ n) (countingDelta y))).trans
    ((rightMarkov s μ ^ n).le_opNorm (countingDelta y))
  rw [rightMarkov_pow_delta, countingDelta_norm, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- A union bound controls the probability of lying in any finite set at time n. -/
theorem walkPosition_finite_probability_le (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (x : Γ) (n : ℕ) (A : Finset Γ) :
    infiniteWalkLaw s μ hμ hmass {ω | walkPosition s x n ω ∈ A} ≤
      ENNReal.ofReal ((A.card : ℝ) * ‖rightMarkov s μ ^ n‖) := by
  have he : {ω : ℕ → s | walkPosition s x n ω ∈ A} =
      ⋃ y ∈ A, {ω | walkPosition s x n ω = y} := by ext ω; simp
  rw [he]
  apply (measure_biUnion_finset_le A (fun y => {ω | walkPosition s x n ω = y})).trans
  simp only [walkPosition_probability s μ hμ hmass]
  calc
    _ ≤ ∑ _y ∈ A, ENNReal.ofReal ‖rightMarkov s μ ^ n‖ :=
      Finset.sum_le_sum (fun y _ => ENNReal.ofReal_le_ofReal (transitionWeight_le_power_norm s μ n x y))
    _ = _ := by simp [ENNReal.ofReal_mul, ENNReal.ofReal_natCast, nsmul_eq_mul]

omit [MeasurableSingletonClass Γ] in
/-- The spectral decay rate can be chosen strictly between zero and one. -/
theorem markov_positive_geometric_rate (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ᶠ n : ℕ in atTop, ‖rightMarkov s μ ^ n‖ ≤ q ^ n := by
  obtain ⟨r, hr0, hr1, hb⟩ := green_powers_geometric_bound (rightMarkov s μ) hgap
  refine ⟨(r + 1) / 2, by linarith, by linarith, ?_⟩
  filter_upwards [hb] with n hn
  exact hn.trans (pow_le_pow_left₀ hr0 (by linarith) n)

/-- Summable real upper bounds imply summability of event probabilities in a finite measure. -/
theorem ae_eventually_notMem_of_real_bound {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (A : ℕ → Set Ω) (b : ℕ → ℝ)
    (hb : Summable b) (hbound : ∀ᶠ n in atTop, ρ (A n) ≤ ENNReal.ofReal (b n)) :
    ∀ᵐ ω ∂ρ, ∀ᶠ n in atTop, ω ∉ A n := by
  have hs : Summable (fun n => (ρ (A n)).toReal) := by
    apply hb.norm.of_norm_bounded_eventually_nat
    filter_upwards [hbound] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _)
      (hn.trans (ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using le_abs_self (b n))))
  apply ae_eventually_notMem
  have he : (∑' n, ρ (A n)) = ENNReal.ofReal (∑' n, (ρ (A n)).toReal) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) hs]
    simp only [ENNReal.ofReal_toReal (measure_ne_top ρ _)]
  rw [he]
  exact ENNReal.ofReal_ne_top

/-- A growth bound on finite target sets combines with spectral decay to give escape. -/
theorem walk_ae_avoid_slow_sets (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (x : Γ)
    (A : ℕ → Finset Γ) (K : ℝ) (hK : 0 ≤ K) (a q : ℝ)
    (hq : 0 ≤ q) (hsmall : Real.exp a * q < 1)
    (hcard : ∀ n, ((A n).card : ℝ) ≤ K * Real.exp (a * n))
    (hpower : ∀ᶠ n : ℕ in atTop, ‖rightMarkov s μ ^ n‖ ≤ q ^ n) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      ∀ᶠ n in atTop, walkPosition s x n ω ∉ A n := by
  apply ae_eventually_notMem_of_real_bound (infiniteWalkLaw s μ hμ hmass)
    (fun n => {ω | walkPosition s x n ω ∈ A n}) (fun n => K * (Real.exp a * q) ^ n)
    ((summable_geometric_of_lt_one (mul_nonneg (Real.exp_pos _).le hq) hsmall).mul_left K)
  filter_upwards [hpower] with n hn
  apply (walkPosition_finite_probability_le s μ hμ hmass x n (A n)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (K * Real.exp (a * n)) * q ^ n :=
      mul_le_mul (hcard n) hn (norm_nonneg _) (mul_nonneg hK (Real.exp_pos _).le)
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul, mul_comm (n : ℝ) a]; ring

end Singularity
