import Singularity.RadonNikodymCoboundary

/-!
# Density bounds from a finite corrected return cover

This is the algebraic and measure-theoretic density-upgrade step. A covering
hypothesis brings almost every point, after one of finitely many corrections,
into a common inverse shadow and then into a bounded-density window. Bounded
magnitude difference along the return sequence then bounds the density.
Constructing that cover is a separate geometric obligation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Singularity

/-- A finite corrected return cover and bounded shadow-magnitude difference
bound the log density on its carrier. The cover is an explicit hypothesis;
absolute continuity alone does not imply this conclusion. -/
theorem logDensity_bound_of_shadow_return_cover {Γ B : Type*} [Group Γ] [Countable Γ]
    [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
    (ν m : Measure B) [IsFiniteMeasure ν] [IsFiniteMeasure m] (hac : ν ≪ m)
    (hν : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) ν ≪ ν)
    (hm : ∀ a : Γ, Measure.map (fun ξ : B => a • ξ) m ≪ m)
    (g : ℕ → Γ) (Sν Sm : ℕ → Set B) (Dν Dm : ℕ → ℝ)
    (F : Finset Γ) (Cν Cm L M J : ℝ)
    (hνshadow : ∀ᵐ ξ ∂ν, ∀ n, ξ ∈ Sν n → |stationaryLogCocycle ν (g n) ξ - Dν n| ≤ Cν)
    (hmshadow : ∀ᵐ ξ ∂ν, ∀ n, ξ ∈ Sm n → |stationaryLogCocycle m (g n) ξ - Dm n| ≤ Cm)
    (hmag : ∀ n, |Dν n - Dm n| ≤ L)
    (hcorrection : ∀ᵐ ξ ∂ν, ∀ a ∈ F,
      |stationaryLogCocycle ν a ξ - stationaryLogCocycle m a ξ| ≤ J)
    (hcover : ∀ᵐ ξ ∂ν, ∃ a ∈ F, ∃ n : ℕ,
      a⁻¹ • ξ ∈ Sν n ∩ Sm n ∧
      |Real.log ((ν.rnDeriv m (g n • (a⁻¹ • ξ))).toReal)| ≤ M) :
    ∀ᵐ ξ ∂ν, |Real.log ((ν.rnDeriv m ξ).toReal)| ≤ M + Cν + Cm + L + J := by
  let H : B → ℝ := fun ξ => Real.log ((ν.rnDeriv m ξ).toReal)
  have hcob : ∀ᵐ ξ ∂ν, ∀ a : Γ,
      stationaryLogCocycle ν a ξ = stationaryLogCocycle m a ξ + H ξ - H (a • ξ) :=
    ae_all_iff.mpr (fun a => stationaryLogCocycle_change_measure ν m hac hν hm a)
  have hbase : ∀ᵐ ξ ∂ν,
      (∀ a : Γ, stationaryLogCocycle ν a ξ = stationaryLogCocycle m a ξ + H ξ - H (a • ξ)) ∧
      (∀ n, ξ ∈ Sν n → |stationaryLogCocycle ν (g n) ξ - Dν n| ≤ Cν) ∧
      (∀ n, ξ ∈ Sm n → |stationaryLogCocycle m (g n) ξ - Dm n| ≤ Cm) ∧
      (∀ a ∈ F, |stationaryLogCocycle ν a ξ - stationaryLogCocycle m a ξ| ≤ J) := by
    filter_upwards [hcob, hνshadow, hmshadow, hcorrection] with ξ hc hv hm hc'
    exact ⟨hc, hv, hm, hc'⟩
  have htrans : ∀ᵐ ξ ∂ν, ∀ a : Γ,
      (∀ b : Γ, stationaryLogCocycle ν b (a⁻¹ • ξ) =
        stationaryLogCocycle m b (a⁻¹ • ξ) + H (a⁻¹ • ξ) - H (b • (a⁻¹ • ξ))) ∧
      (∀ n, a⁻¹ • ξ ∈ Sν n → |stationaryLogCocycle ν (g n) (a⁻¹ • ξ) - Dν n| ≤ Cν) ∧
      (∀ n, a⁻¹ • ξ ∈ Sm n → |stationaryLogCocycle m (g n) (a⁻¹ • ξ) - Dm n| ≤ Cm) ∧
      (∀ b ∈ F, |stationaryLogCocycle ν b (a⁻¹ • ξ) - stationaryLogCocycle m b (a⁻¹ • ξ)| ≤ J) := by
    apply ae_all_iff.mpr
    intro a
    exact (show Measure.QuasiMeasurePreserving (fun ξ : B => a⁻¹ • ξ) ν ν from
      ⟨measurable_const_smul a⁻¹, hν a⁻¹⟩).ae hbase
  filter_upwards [htrans, hcover] with ξ hgood hreturn
  obtain ⟨a, ha, n, hn, hwindow⟩ := hreturn
  obtain ⟨hc, hv, hm', hj⟩ := hgood a
  have hreturnCocycle := hc (g n)
  have hcorrectionCocycle := hc a
  simp only [smul_inv_smul] at hcorrectionCocycle
  rcases abs_le.mp (hv n hn.1) with ⟨hvl, hvu⟩
  rcases abs_le.mp (hm' n hn.2) with ⟨hml, hmu⟩
  rcases abs_le.mp (hmag n) with ⟨hdl, hdu⟩
  rcases abs_le.mp (hj a ha) with ⟨hjl, hju⟩
  change |H (g n • (a⁻¹ • ξ))| ≤ M at hwindow
  rcases abs_le.mp hwindow with ⟨hwl, hwu⟩
  change |H ξ| ≤ _
  apply abs_le.mpr
  constructor <;> linarith

end Singularity
