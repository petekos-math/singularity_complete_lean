import Singularity.HyperbolicOrbitGrowth
import Singularity.SpectralEscape
import Singularity.GeometricPathConvergence

/-!
# Full geometric convergence from discreteness and the operator spectral gap

The exponential orbit-count bound and uniform spectral decay imply almost-sure
positive linear escape by Borel--Cantelli. Finite support bounds hyperbolic jumps;
the Cayley estimate then proves full compact convergence. This constructs the
geometric hitting law independently of the Green distance comparison.

The nonamenability-to-spectral-gap criterion remains a separate obligation.
-/

noncomputable section
open MeasureTheory Filter Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane

namespace Singularity

/-- A sufficiently small positive escape rate is dominated by spectral decay. -/
theorem exists_positive_escape_rate {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ a : ℝ, 0 < a ∧ Real.exp (4 * a) * q < 1 := by
  have hl : Real.log q < 0 := Real.log_neg hq hq1
  refine ⟨-Real.log q / 8, by linarith, ?_⟩
  have he : Real.exp (4 * (-Real.log q / 8)) * q = Real.exp (Real.log q / 2) := by
    calc
      _ = Real.exp (4 * (-Real.log q / 8)) * Real.exp (Real.log q) := by rw [Real.exp_log hq]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  rw [he]
  exact Real.exp_lt_one_iff.mpr (by linarith)

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]

/-- Almost every sample path escapes linearly in the hyperbolic metric. -/
theorem walk_ae_hyperbolic_linear_escape (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) :
    ∃ a : ℝ, 0 < a ∧ ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      ∀ᶠ n : ℕ in atTop,
        a * n ≤ dist (walkPosition s x n ω • UpperHalfPlane.I) UpperHalfPlane.I := by
  obtain ⟨q, hq0, hq1, hpower⟩ := markov_positive_geometric_rate s μ hgap
  obtain ⟨a, ha, hsmall⟩ := exists_positive_escape_rate hq0 hq1
  have hcard (n : ℕ) : ((hyperbolicOrbitBall Γ (a * n)).card : ℝ) ≤
      (49 * (hyperbolicOrbitBall Γ 2).card) * Real.exp ((4 * a) * n) := by
    simpa only [mul_assoc] using hyperbolicOrbitBall_card Γ (R := a * n) (by positivity)
  have h := walk_ae_avoid_slow_sets s μ hμ hmass x
    (fun n => hyperbolicOrbitBall Γ (a * n)) (49 * (hyperbolicOrbitBall Γ 2).card)
    (by positivity) (4 * a) q hq0.le hsmall hcard hpower
  refine ⟨a, ha, ?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  exact (lt_of_not_ge ((mem_hyperbolicOrbitBall Γ (a * n) _).not.mp hn)).le

omit [DiscreteTopology Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ] in
/-- Changing the initial point in the half-plane changes radial distance by a bounded amount. -/
theorem orbit_radial_basepoint_bound (g : Γ) (z : ℍ) :
    dist (g • UpperHalfPlane.I) UpperHalfPlane.I ≤
      dist (g • z) UpperHalfPlane.I + dist z UpperHalfPlane.I := by
  have h := dist_triangle (g • UpperHalfPlane.I) (g • z) UpperHalfPlane.I
  change dist (((g : SL(2, ℝ)) • UpperHalfPlane.I)) UpperHalfPlane.I ≤
    dist (((g : SL(2, ℝ)) • UpperHalfPlane.I)) (((g : SL(2, ℝ)) • z)) +
      dist (g • z) UpperHalfPlane.I at h
  rw [dist_smul (g : SL(2, ℝ))] at h
  change dist (g • UpperHalfPlane.I) UpperHalfPlane.I ≤
    dist UpperHalfPlane.I z + dist (g • z) UpperHalfPlane.I at h
  simpa only [dist_comm UpperHalfPlane.I z, add_comm] using h

/-- Radial exponential weights are summable on almost every actual path. -/
theorem walk_ae_hyperbolic_radial_summable (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) (z : ℍ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      Summable (fun n => Real.exp (-dist (walkPosition s x n ω • z) UpperHalfPlane.I)) := by
  obtain ⟨a, ha, h⟩ := walk_ae_hyperbolic_linear_escape Γ s μ hμ hmass hgap x
  filter_upwards [h] with ω hω
  apply summable_radial_of_linear_escape (fun n => walkPosition s x n ω • z) ha
    (dist z UpperHalfPlane.I)
  filter_upwards [hω] with n hn
  have hb := orbit_radial_basepoint_bound Γ (walkPosition s x n ω) z
  linarith

/-- Full compact convergence, independent of any Green-distance comparison. -/
theorem walk_ae_geometric_convergence (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) (z : ℍ) :
    ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
      ∃ p : OnePoint ℂ, Tendsto
        (fun n => hyperbolicCompactEmbedding (walkPosition s x n ω • z)) atTop (nhds p) :=
  walk_ae_compact_convergence_of_summable_escape Γ s μ hμ hmass x z
    (walk_ae_hyperbolic_radial_summable Γ s μ hμ hmass hgap x z)

/-- The genuine geometric hitting law, with convergence now proved from the spectral gap. -/
theorem exists_geometric_hittingLaw (s : Finset Γ) (μ : Γ → ℝ)
    (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ) :
    ∃ b : (ℕ → s) → OnePoint ℂ, Measurable b ∧
      (∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
        Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z))
          atTop (nhds (b ω))) ∧
      let ν := walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b
      IsProbabilityMeasure ν ∧ ν compactHyperbolicBoundary = 1 ∧
      ν = (∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun p : OnePoint ℂ => (g : Γ) • p) ν) ∧
      ∀ g : Γ, Measure.map (fun p : OnePoint ℂ => g • p) ν ≪ ν ∧
        ν ≪ Measure.map (fun p : OnePoint ℂ => g • p) ν :=
  exists_compact_geometric_hittingLaw Γ s μ hpos hmass hgen hgap z
    (walk_ae_geometric_convergence Γ s μ (fun g hg => (hpos g hg).le) hmass hgap 1 z)

end Singularity
