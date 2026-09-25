import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# The contraction argument for fixed vectors

For an isometric group action, an element whose conjugates converge to the
identity fixes every vector fixed by the conjugating elements, provided its
orbit map is continuous at the identity. This is the metric form of the
Mautner argument. No Hilbert-space or ergodicity conclusion is assumed.
-/

noncomputable section
open Filter
open scoped Topology

namespace Singularity

/-- Contraction of conjugates forces a fixed vector for a strongly continuous isometric action. -/
theorem fixed_of_conjugates_tendsto_one {G X ι : Type*} [Group G] [TopologicalSpace G]
    [MetricSpace X] [MulAction G X] [IsIsometricSMul G X]
    {l : Filter ι} [l.NeBot] (a : ι → G) (g : G) (v : X)
    (hcont : ContinuousAt (fun h : G => h • v) 1)
    (hfix : ∀ i, a i • v = v)
    (hcontract : Tendsto (fun i => (a i)⁻¹ * g * a i) l (nhds 1)) : g • v = v := by
  have hfixinv (i : ι) : (a i)⁻¹ • v = v := by
    exact inv_smul_eq_iff.mpr (hfix i).symm
  have hd (i : ι) : dist (((a i)⁻¹ * g * a i) • v) v = dist (g • v) v := by
    rw [mul_smul, mul_smul, hfix i]
    calc
      dist ((a i)⁻¹ • (g • v)) v = dist ((a i)⁻¹ • (g • v)) ((a i)⁻¹ • v) := by rw [hfixinv]
      _ = dist (g • v) v := dist_smul _ _ _
  have ht := (hcont.tendsto.comp hcontract).dist (tendsto_const_nhds (x := v))
  simp only [Function.comp_def, one_smul, hd, dist_self] at ht
  exact dist_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds ht)

/-- Fixing one group element implies fixing every positive and negative integral power. -/
theorem fixed_zpow_of_fixed {G X : Type*} [Group G] [MulAction G X]
    (g : G) (v : X) (hfix : g • v = v) (n : ℤ) : g ^ n • v = v :=
  MulAction.mem_fixedBy_zpow hfix n

end Singularity
