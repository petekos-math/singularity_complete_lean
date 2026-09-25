import Singularity.WeightedCurrent
import Singularity.StationaryDensity

/-!
# Current covariance using actual Radon--Nikodym derivatives

The cancellation argument needs positive densities only almost everywhere,
which is what Radon--Nikodym derivatives provide. Stationarity and semigroup
generation supply the derivative reconstruction and positivity; these are no
longer separate hypotheses of the current-invariance implication.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Classical

namespace Singularity

/-- Almost-everywhere positivity suffices for the real-kernel cancellation rule. -/
theorem weightedProduct_invariant_of_div_ae {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ X) (f : Y ≃ᵐ Y) (α : Measure X) (β : Measure Y) [SFinite α] [SFinite β]
    (rX : X → ℝ) (rY : Y → ℝ) (K : X × Y → ℝ)
    (hrX : Measurable rX) (hrY : Measurable rY) (hK : Measurable K)
    (hpX : ∀ᵐ x ∂α, 0 < rX x) (hpY : ∀ᵐ y ∂β, 0 < rY y)
    (hα : Measure.map e α = α.withDensity (fun x => ENNReal.ofReal (rX x)))
    (hβ : Measure.map f β = β.withDensity (fun y => ENNReal.ofReal (rY y)))
    (hc : ∀ᵐ p ∂α.prod β, K (e.symm p.1, f.symm p.2) = K p / (rX p.1 * rY p.2)) :
    Measure.map (e.prodCongr f) ((α.prod β).withDensity (fun p => ENNReal.ofReal (K p))) =
      (α.prod β).withDensity (fun p => ENNReal.ofReal (K p)) := by
  apply weightedProduct_invariant e f α β _ _ _
    hrX.ennreal_ofReal hrY.ennreal_ofReal hK.ennreal_ofReal hα hβ
  filter_upwards [hc, Measure.quasiMeasurePreserving_fst.ae hpX,
    Measure.quasiMeasurePreserving_snd.ae hpY] with p hp hx hy
  rw [← ENNReal.ofReal_mul hx.le, ← ENNReal.ofReal_mul (mul_pos hx hy).le]
  congr 1
  rw [hp]
  field_simp [hx.ne', hy.ne']

variable {Γ X Y : Type*} [Group Γ]
  [MeasurableSpace X] [MulAction Γ X] [MeasurableConstSMul Γ X]
  [MeasurableSpace Y] [MulAction Γ Y] [MeasurableConstSMul Γ Y]

/-- The real-valued density still reconstructs the actual translated stationary law. -/
theorem stationaryRealDensity_withDensity (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    (α : Measure X) [IsFiniteMeasure α]
    (hs : α = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun x : X => (g : Γ) • x) α)
    (g : Γ) : α.withDensity (fun x => ENNReal.ofReal (stationaryRealDensity α g x)) =
      Measure.map (fun x : X => g • x) α := by
  rw [← stationaryDensity_withDensity s μ hμ hgen α hs]
  apply withDensity_congr_ae
  filter_upwards [stationaryDensity_positive_finite s μ hμ hgen α hs g] with x hx
  exact ENNReal.ofReal_toReal hx.2.ne

/-- A covariance law in the actual hitting derivatives yields an invariant current.
The two marginals may be stationary for different finite jump laws. -/
theorem stationary_weightedProduct_invariant
    (s t : Finset Γ) (μ ν : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) (hν : ∀ g ∈ t, 0 < ν g)
    (hgs : Submonoid.closure (s : Set Γ) = ⊤) (hgt : Submonoid.closure (t : Set Γ) = ⊤)
    (α : Measure X) (β : Measure Y) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hs : α = ∑ g : s, ENNReal.ofReal (μ g) • Measure.map (fun x : X => (g : Γ) • x) α)
    (ht : β = ∑ g : t, ENNReal.ofReal (ν g) • Measure.map (fun y : Y => (g : Γ) • y) β)
    (K : X × Y → ℝ) (hK : Measurable K) (g : Γ)
    (hc : ∀ᵐ p ∂α.prod β, K (g⁻¹ • p.1, g⁻¹ • p.2) =
      K p / (stationaryRealDensity α g p.1 * stationaryRealDensity β g p.2)) :
    Measure.map (fun p : X × Y => (g • p.1, g • p.2))
      ((α.prod β).withDensity (fun p => ENNReal.ofReal (K p))) =
      (α.prod β).withDensity (fun p => ENNReal.ofReal (K p)) := by
  apply weightedProduct_invariant_of_div_ae (MeasurableEquiv.smul g) (MeasurableEquiv.smul g)
    α β (stationaryRealDensity α g) (stationaryRealDensity β g) K
    (measurable_stationaryDensity α g).ennreal_toReal
    (measurable_stationaryDensity β g).ennreal_toReal hK
  · filter_upwards [stationaryDensity_positive_finite s μ hμ hgs α hs g] with x hx
    exact ENNReal.toReal_pos hx.1.ne' hx.2.ne
  · filter_upwards [stationaryDensity_positive_finite t ν hν hgt β ht g] with y hy
    exact ENNReal.toReal_pos hy.1.ne' hy.2.ne
  · exact (stationaryRealDensity_withDensity s μ hμ hgs α hs g).symm
  · exact (stationaryRealDensity_withDensity t ν hν hgt β ht g).symm
  · exact hc

end Singularity
