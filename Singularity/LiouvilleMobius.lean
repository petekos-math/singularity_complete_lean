import Singularity.LiouvilleTransformations

/-!
# Möbius invariance of the finite-chart Liouville measure

The elementary invariances are composed using the affine/inversion
factorization of a real special-linear matrix. Exceptional poles are removed
using absolute continuity of the current relative to product Lebesgue measure.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical MatrixGroups

namespace Singularity

/-- Composition preserves simultaneous-endpoint invariance. -/
theorem realLiouvilleMeasure_comp (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Measure.map (Prod.map f f) realLiouvilleMeasure = realLiouvilleMeasure)
    (hgi : Measure.map (Prod.map g g) realLiouvilleMeasure = realLiouvilleMeasure) :
    Measure.map (Prod.map (f ∘ g) (f ∘ g)) realLiouvilleMeasure = realLiouvilleMeasure := by
  have h := congrArg (Measure.map (Prod.map f f)) hgi
  rw [Measure.map_map (hf.prodMap hf) (hg.prodMap hg), hfi] at h
  exact h

/-- Affine invariance follows from positive dilation and translation. -/
theorem realLiouvilleMeasure_affine (a v : ℝ) (ha : 0 < a) :
    Measure.map (fun p : ℝ × ℝ => (v + a * p.1, v + a * p.2)) realLiouvilleMeasure = realLiouvilleMeasure :=
  realLiouvilleMeasure_comp (fun x => v + x) (fun x => a * x)
    (measurable_const_add v) (measurable_const_mul a)
    (realLiouvilleMeasure_translate v) (realLiouvilleMeasure_dilate a ha)

/-- The inversion word used in the Bruhat factorization preserves the current. -/
theorem realLiouvilleMeasure_word (a v w : ℝ) (ha : 0 < a) :
    Measure.map (fun p : ℝ × ℝ =>
      (w + boundaryInversion (v + a * p.1), w + boundaryInversion (v + a * p.2)))
      realLiouvilleMeasure = realLiouvilleMeasure := by
  have h := realLiouvilleMeasure_comp boundaryInversion (fun x => v + a * x)
    measurable_boundaryInversion (by fun_prop) realLiouvilleMeasure_invert
    (realLiouvilleMeasure_affine a v ha)
  exact realLiouvilleMeasure_comp (fun x => w + x) (boundaryInversion ∘ fun x => v + a * x)
    (measurable_const_add w) (measurable_boundaryInversion.comp (by fun_prop)) (realLiouvilleMeasure_translate w) h

/-- Null changes to a boundary map are null changes for the absolutely continuous pair current. -/
theorem realLiouvilleMeasure_map_congr (f g : ℝ → ℝ) (hfg : f =ᵐ[volume] g) :
    Measure.map (Prod.map f f) realLiouvilleMeasure = Measure.map (Prod.map g g) realLiouvilleMeasure := by
  apply Measure.map_congr
  apply realLiouvilleMeasure_absolutelyContinuous.ae_eq
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hfg,
    Measure.quasiMeasurePreserving_snd.ae hfg] with p hx hy
  exact Prod.ext hx hy

set_option backward.isDefEq.respectTransparency false in
/-- Every real special-linear Möbius transformation preserves the finite-chart current. -/
theorem realLiouvilleMeasure_mobius (g : SL(2, ℝ)) :
    Measure.map (Prod.map (realBoundaryMobius g) (realBoundaryMobius g)) realLiouvilleMeasure =
      realLiouvilleMeasure := by
  by_cases hc : g 1 0 = 0
  · obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
    let G : SL(2, ℝ) := ⟨!![a, b; 0, a⁻¹], by simp [ha]⟩
    change Measure.map (Prod.map (realBoundaryMobius G) (realBoundaryMobius G)) realLiouvilleMeasure = _
    have hb : realBoundaryMobius G = (fun u => b * a + (a * a) * u) := by
      funext u
      simp [realBoundaryMobius, G, div_inv_eq_mul]
      ring
    rw [hb]
    exact realLiouvilleMeasure_affine (a * a) (b * a) (mul_self_pos.mpr ha)
  · induction g using Matrix.SpecialLinearGroup.fin_two_induction with | h a b c d hdet =>
    have hc' : c ≠ 0 := by simpa using hc
    let G : SL(2, ℝ) := ⟨!![a, b; c, d], by simpa using hdet⟩
    change Measure.map (Prod.map (realBoundaryMobius G) (realBoundaryMobius G)) realLiouvilleMeasure = _
    have hb : realBoundaryMobius G =ᵐ[volume]
        (fun u => a / c + boundaryInversion (c * d + (c * c) * u)) := by
      have hz : ∀ᵐ u : ℝ ∂volume, u ≠ -d / c := by simp [ae_iff]
      filter_upwards [hz] with u hu
      have hd : c * u + d ≠ 0 := by
        intro hh
        apply hu
        apply (eq_div_iff hc').mpr
        nlinarith
      change (a * u + b) / (c * u + d) = a / c + -(c * d + c * c * u)⁻¹
      grind
    rw [realLiouvilleMeasure_map_congr _ _ hb]
    exact realLiouvilleMeasure_word (c * c) (c * d) (a / c) (mul_self_pos.mpr hc')

end Singularity
