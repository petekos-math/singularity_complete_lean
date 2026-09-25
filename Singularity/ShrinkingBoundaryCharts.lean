import Singularity.IntervalBoundaryCharts
import Singularity.ParabolicIdealLimits

/-!
# Shrinking charts with endpoints in a dense boundary set

Every neighborhood of an ideal point contains a closed chart arc whose
endpoints belong to a prescribed dense set and whose interior contains
that point. Applied to parabolic fixed points, this constructs shrinking
cusp arcs for groups whose ideal limit set is the entire boundary.
-/

noncomputable section
open Set OnePoint Filter
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- A dense supply of endpoints gives arbitrarily small closed chart arcs
around every ideal point, with strictly negative center coordinate. -/
theorem exists_small_boundary_chart_of_dense
    (D : Set (OnePoint ℝ)) (hD : Dense D) (ξ : OnePoint ℝ)
    (U : Set (OnePoint ℝ)) (hU : IsOpen U) (hξU : ξ ∈ U) :
    ∃ B : SL(2, ℝ), B • (∞ : OnePoint ℝ) ∈ D ∧
      B • ((0 : ℝ) : OnePoint ℝ) ∈ D ∧ chartNonpositiveBoundaryArc B ⊆ U ∧
      ∃ t : ℝ, t < 0 ∧ B⁻¹ • ξ = (t : OnePoint ℝ) := by
  obtain ⟨A, hA⟩ := exists_slTwo_chart_at_boundary ξ
  let C := A * boundaryPoleMatrix 0
  have hC : C • ((0 : ℝ) : OnePoint ℝ) = ξ := by
    have hj : boundaryPoleMatrix 0 • ((0 : ℝ) : OnePoint ℝ) = ∞ := by
      apply compactBoundary_smul_pole
      simp [boundaryPoleMatrix]
    dsimp [C]
    rw [mul_smul, hj, hA]
  let f : ℝ → OnePoint ℝ := fun x => C • (x : OnePoint ℝ)
  have hf : Continuous f := (continuous_const_smul C).comp OnePoint.continuous_coe
  have h0 : (0 : ℝ) ∈ f ⁻¹' U := by
    change C • ((0 : ℝ) : OnePoint ℝ) ∈ U
    rwa [hC]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ((hU.preimage hf).mem_nhds h0)
  have hfind (a b : ℝ) (hab : a < b) : ∃ x ∈ Ioo a b, f x ∈ D := by
    have hopen : IsOpen ((fun η : OnePoint ℝ => C • η) '' (((↑) : ℝ → OnePoint ℝ) '' Ioo a b)) :=
      (Homeomorph.smul C).isOpenMap _ (OnePoint.isOpen_image_coe.mpr isOpen_Ioo)
    have hne : ((fun η : OnePoint ℝ => C • η) '' (((↑) : ℝ → OnePoint ℝ) '' Ioo a b)).Nonempty :=
      ((nonempty_Ioo.mpr hab).image ((↑) : ℝ → OnePoint ℝ)).image _
    obtain ⟨η, hηD, η', ⟨x, hx, rfl⟩, rfl⟩ := hD.exists_mem_open hopen hne
    exact ⟨x, hx, hηD⟩
  obtain ⟨l, hl, hlD⟩ := hfind (-ε / 2) 0 (by linarith)
  obtain ⟨r, hr, hrD⟩ := hfind 0 (ε / 2) (by linarith)
  have hlr : l < r := hl.2.trans hr.1
  let B := intervalBoundaryChart l r hlr
  obtain ⟨hBl, hBr⟩ := intervalBoundaryChart_endpoints l r hlr
  refine ⟨C * B, ?_, ?_, ?_, ?_⟩
  · simpa only [B, mul_smul, hBl] using hlD
  · simpa only [B, mul_smul, hBr] using hrD
  · intro η hη
    have hpre : C⁻¹ • η ∈ chartNonpositiveBoundaryArc B := by
      simpa only [chartNonpositiveBoundaryArc, mem_preimage, mul_inv_rev, mul_smul] using hη
    obtain ⟨t, ht, he⟩ := chartNonpositiveBoundaryArc_interval_subset l r hlr hpre
    have hηeq : η = f t := by
      have hh := congrArg (fun p : OnePoint ℝ => C • p) he
      simpa only [smul_inv_smul] using hh.symm
    rw [hηeq]
    apply hball
    change dist t 0 < ε
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2, hl.1, hr.2]
  · obtain ⟨t, ht, he⟩ := intervalBoundaryChart_negative_coordinate l r hlr ⟨hl.2, hr.1⟩
    refine ⟨t, ht, ?_⟩
    rw [mul_inv_rev, mul_smul, ← hC, inv_smul_smul]
    exact he

/-- If a nonelementary group has full ideal boundary and a parabolic,
every ideal neighborhood contains a cusp chart arc around its center. -/
theorem exists_small_parabolic_boundary_chart
    (Γ : Subgroup PSL(2, ℝ)) (hne : ProjectiveNonelementary Γ) (z : ℍ)
    (hfull : projectiveOrbitLimitSet Γ z = univ)
    (hpar : ∃ g : Γ, ProjectiveParabolic (g : PSL(2, ℝ)))
    (ξ : OnePoint ℝ) (U : Set (OnePoint ℝ)) (hU : IsOpen U) (hξU : ξ ∈ U) :
    ∃ B : SL(2, ℝ), B • (∞ : OnePoint ℝ) ∈ projectiveParabolicFixedPoints Γ ∧
      B • ((0 : ℝ) : OnePoint ℝ) ∈ projectiveParabolicFixedPoints Γ ∧
      chartNonpositiveBoundaryArc B ⊆ U ∧
      ∃ t : ℝ, t < 0 ∧ B⁻¹ • ξ = (t : OnePoint ℝ) := by
  apply exists_small_boundary_chart_of_dense _ _ ξ U hU hξU
  intro p
  rw [closure_projectiveParabolicFixedPoints_eq_limitSet Γ hne z hpar, hfull]
  trivial

end Singularity
