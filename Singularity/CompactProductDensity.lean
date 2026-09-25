import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounds for factors of a continuous off-diagonal product

On a compact Hausdorff space with a nonatomic probability, if f(x)g(y)
is almost everywhere a positive continuous function away from the diagonal,
then both factors are bounded above and away from zero almost everywhere,
provided they are positive almost everywhere. Two distinct good sections and
disjoint neighborhoods of their anchor points cover the whole space.
-/

noncomputable section
open MeasureTheory Filter Set

namespace Singularity

/-- A positive continuous section has positive lower and finite upper bounds on a compact set avoiding its anchor. -/
theorem compact_positive_section_bounds {X : Type*} [TopologicalSpace X]
    (H : X × X → ℝ)
    (hH : ContinuousOn H {p | p.1 ≠ p.2})
    (hp : ∀ x y, x ≠ y → 0 < H (x, y))
    (y : X) (d : ℝ) (hd : 0 < d)
    {C : Set X} (hC : IsCompact C) (hne : C.Nonempty) (hy : y ∉ C) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x ∈ C, a ≤ H (x, y) / d ∧ H (x, y) / d ≤ b := by
  have hc : ContinuousOn (fun x => H (x, y) / d) C :=
    (hH.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => y))).continuousOn
      (fun x hx => fun (he : x = y) => hy (he ▸ hx))).div_const d
  obtain ⟨u, hu, hmin⟩ := hC.exists_isMinOn hne hc
  obtain ⟨v, hv, hmax⟩ := hC.exists_isMaxOn hne hc
  refine ⟨H (u, y) / d, H (v, y) / d, ?_, ?_, fun x hx => ⟨hmin hx, hmax hx⟩⟩
  · exact div_pos (hp u y (fun h => hy (h ▸ hu))) hd
  · exact div_pos (hp v y (fun h => hy (h ▸ hv))) hd

/-- A product density continuous and positive off the diagonal forces uniform a.e. bounds on its first factor. -/
theorem compact_product_density_first_bounds {X : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m] [NullSingletonClass m]
    (f g : X → ℝ) (H : X × X → ℝ)
    (hH : ContinuousOn H {p | p.1 ≠ p.2})
    (hp : ∀ x y, x ≠ y → 0 < H (x, y))
    (hg : ∀ᵐ y ∂m, 0 < g y)
    (heq : ∀ᵐ p ∂m.prod m, f p.1 * g p.2 = H p) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᵐ x ∂m, a ≤ f x ∧ f x ≤ b := by
  have hsec : ∀ᵐ y ∂m, ∀ᵐ x ∂m, f x * g y = H (x, y) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae heq)
  obtain ⟨y, hgy, hey⟩ := (hg.and hsec).exists
  obtain ⟨z, ⟨hgz, hez⟩, hzy⟩ := ((hg.and hsec).and (m.ae_ne y)).exists
  obtain ⟨U, V, hU, hV, hyU, hzV, hdis⟩ := t2_separation hzy.symm
  have hzU : z ∉ U := fun hzU => Set.disjoint_left.mp hdis hzU hzV
  have hyV : y ∉ V := fun hyV => Set.disjoint_left.mp hdis hyU hyV
  obtain ⟨a, b, ha, hb, hab⟩ := compact_positive_section_bounds H hH hp y (g y) hgy
    hU.isClosed_compl.isCompact ⟨z, hzU⟩ (not_not.mpr hyU)
  obtain ⟨c, d, hc, hd, hcd⟩ := compact_positive_section_bounds H hH hp z (g z) hgz
    hV.isClosed_compl.isCompact ⟨y, hyV⟩ (not_not.mpr hzV)
  refine ⟨min a c, max b d, lt_min ha hc, lt_max_of_lt_left hb, ?_⟩
  filter_upwards [hey, hez] with x hxy hxz
  by_cases hx : x ∈ U
  · have hxV : x ∈ Vᶜ := fun hxV => Set.disjoint_left.mp hdis hx hxV
    have hxf : f x = H (x, z) / g z := (eq_div_iff hgz.ne').mpr hxz
    rw [hxf]
    exact ⟨(min_le_right _ _).trans (hcd x hxV).1, (hcd x hxV).2.trans (le_max_right _ _)⟩
  · have hxf : f x = H (x, y) / g y := (eq_div_iff hgy.ne').mpr hxy
    rw [hxf]
    exact ⟨(min_le_left _ _).trans (hab x hx).1, (hab x hx).2.trans (le_max_left _ _)⟩

/-- Both factors admit common positive lower and finite upper bounds. -/
theorem compact_product_density_bounds {X : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m] [NullSingletonClass m]
    (f g : X → ℝ) (H : X × X → ℝ)
    (hH : ContinuousOn H {p | p.1 ≠ p.2})
    (hp : ∀ x y, x ≠ y → 0 < H (x, y))
    (hg : ∀ᵐ y ∂m, 0 < g y)
    (heq : ∀ᵐ p ∂m.prod m, f p.1 * g p.2 = H p) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ᵐ x ∂m, (a ≤ f x ∧ f x ≤ b) ∧ (a ≤ g x ∧ g x ≤ b) := by
  obtain ⟨a, b, ha, hb, hf⟩ := compact_product_density_first_bounds m f g H hH hp hg heq
  have hfp : ∀ᵐ x ∂m, 0 < f x := hf.mono (fun _ hx => ha.trans_le hx.1)
  have hc : ContinuousOn (fun p : X × X => H p.swap) {p | p.1 ≠ p.2} :=
    hH.comp continuous_swap.continuousOn (fun p hp => Ne.symm hp)
  have hs : ∀ᵐ p ∂m.prod m, g p.1 * f p.2 = H p.swap := by
    filter_upwards [Measure.measurePreserving_swap.quasiMeasurePreserving.ae heq] with p hp
    simpa only [Prod.fst_swap, Prod.snd_swap, mul_comm] using hp
  obtain ⟨c, d, hc, hd, hgg⟩ := compact_product_density_first_bounds m g f _ hc
    (fun x y hxy => hp y x hxy.symm) hfp hs
  refine ⟨min a c, max b d, lt_min ha hc, lt_max_of_lt_left hb, ?_⟩
  filter_upwards [hf, hgg] with x hx hy
  exact ⟨⟨(min_le_left _ _).trans hx.1, hx.2.trans (le_max_left _ _)⟩,
    ⟨(min_le_right _ _).trans hy.1, hy.2.trans (le_max_right _ _)⟩⟩

end Singularity
