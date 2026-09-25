import Singularity.CocycleShadowMeasure

/-!
# Measurable shadows defined by the actual cocycle deficit

These are concrete sets defined from the Radon–Nikodym cocycle. Their local
cocycle estimates follow from the definition and a global upper bound.
Exhaustion for each group element does not assert uniform exhaustion over
the group or topological exceptional-set convergence.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace B] [MulAction Γ B]
  [MeasurableConstSMul Γ B]

/-- A target point belongs to the shadow when the cocycle at its inverse
translate is within R below the prescribed magnitude. -/
def cocycleDeficitShadow (ν : Measure B) (D : Γ → ℝ) (R : ℝ) (g : Γ) : Set B :=
  {η | D g - stationaryLogCocycle ν g (g⁻¹ • η) ≤ R}

omit [MeasurableConstSMul Γ B] in
/-- The inverse shadow is exactly the sublevel set of the cocycle deficit. -/
theorem preimage_cocycleDeficitShadow (ν : Measure B) (D : Γ → ℝ) (R : ℝ) (g : Γ) :
    (fun ξ : B => g • ξ) ⁻¹' cocycleDeficitShadow ν D R g =
      {ξ | D g - stationaryLogCocycle ν g ξ ≤ R} := by
  ext ξ
  simp only [mem_preimage, cocycleDeficitShadow, mem_ofPred_eq, inv_smul_smul]

/-- Deficit shadows are measurable even without continuity of the cocycle. -/
theorem measurableSet_cocycleDeficitShadow (ν : Measure B) (D : Γ → ℝ) (R : ℝ) (g : Γ) :
    MeasurableSet (cocycleDeficitShadow ν D R g) :=
  measurableSet_le (measurable_const.sub
    ((measurable_stationaryLogCocycle ν g).comp (measurable_const_smul g⁻¹))) measurable_const

omit [MeasurableConstSMul Γ B] in
/-- Increasing the deficit allowance enlarges the shadow. -/
theorem cocycleDeficitShadow_mono (ν : Measure B) (D : Γ → ℝ) (g : Γ) :
    Monotone (fun R => cocycleDeficitShadow ν D R g) :=
  fun _ _ h _ hξ => hξ.trans h

omit [MeasurableConstSMul Γ B] in
/-- Integer deficit allowances exhaust all target points for each fixed element. -/
theorem iUnion_cocycleDeficitShadow (ν : Measure B) (D : Γ → ℝ) (g : Γ) :
    (⋃ N : ℕ, cocycleDeficitShadow ν D N g) = univ := by
  apply eq_univ_of_forall
  intro ξ
  obtain ⟨N, hN⟩ := exists_nat_ge (D g - stationaryLogCocycle ν g (g⁻¹ • ξ))
  exact mem_iUnion.mpr ⟨N, hN⟩

omit [MeasurableConstSMul Γ B] in
/-- A global upper cocycle bound turns the deficit condition into the desired
two-sided local approximation, almost everywhere on the inverse shadow. -/
theorem cocycleDeficitShadow_logCocycle_bound (ν : Measure B) (D : Γ → ℝ)
    (g : Γ) {R : ℝ} (hR : 0 ≤ R)
    (hupper : ∀ᵐ ξ ∂ν, stationaryLogCocycle ν g ξ ≤ D g) :
    ∀ᵐ ξ ∂ν, g • ξ ∈ cocycleDeficitShadow ν D R g →
      |stationaryLogCocycle ν g ξ - D g| ≤ R := by
  filter_upwards [hupper] with ξ hξ hmem
  change D g - stationaryLogCocycle ν g (g⁻¹ • (g • ξ)) ≤ R at hmem
  rw [inv_smul_smul] at hmem
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The explicit shadow definition provides exponential estimates with the
inverse-shadow mass retained. -/
theorem cocycleDeficitShadow_mass_bounds (ν : Measure B) [IsFiniteMeasure ν]
    (hq : ∀ g : Γ, Measure.map (fun ξ : B => g • ξ) ν ≪ ν)
    (D : Γ → ℝ) (g : Γ) {R : ℝ} (hR : 0 ≤ R)
    (hupper : ∀ᵐ ξ ∂ν, stationaryLogCocycle ν g ξ ≤ D g) :
    ENNReal.ofReal (Real.exp (-D g - R)) *
        ν {ξ | D g - stationaryLogCocycle ν g ξ ≤ R} ≤ ν (cocycleDeficitShadow ν D R g) ∧
      ν (cocycleDeficitShadow ν D R g) ≤ ENNReal.ofReal (Real.exp (-D g + R)) *
        ν {ξ | D g - stationaryLogCocycle ν g ξ ≤ R} := by
  have h := shadow_mass_bounds_of_logCocycle ν hq g
    (measurableSet_cocycleDeficitShadow ν D R g) (D g) R
    (cocycleDeficitShadow_logCocycle_bound ν D g hR hupper)
  simpa only [preimage_cocycleDeficitShadow] using h

omit [MeasurableConstSMul Γ B] in
/-- For one fixed element the inverse-shadow masses tend to total mass.
The assertion is deliberately pointwise in g, not uniform over the group. -/
theorem inverse_cocycleDeficitShadow_mass_tendsto (ν : Measure B) (D : Γ → ℝ) (g : Γ) :
    Tendsto (fun N : ℕ => ν ((fun ξ : B => g • ξ) ⁻¹' cocycleDeficitShadow ν D N g))
      atTop (𝓝 (ν univ)) := by
  have hmono : Monotone (fun N : ℕ =>
      (fun ξ : B => g • ξ) ⁻¹' cocycleDeficitShadow ν D N g) :=
    fun _ _ h => preimage_mono (cocycleDeficitShadow_mono ν D g (by exact_mod_cast h))
  have he : (⋃ N : ℕ, (fun ξ : B => g • ξ) ⁻¹' cocycleDeficitShadow ν D N g) = univ := by
    rw [← preimage_iUnion, iUnion_cocycleDeficitShadow, preimage_univ]
  simpa only [he, Function.comp_def] using tendsto_measure_iUnion_atTop (μ := ν) hmono

end Singularity
