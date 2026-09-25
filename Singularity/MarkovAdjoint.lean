import Singularity.Markov
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The reflected law and the right Markov adjoint

These identities hold for arbitrary real finite weights. Neither symmetry,
laziness, nor a spectral gap is required.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]

/-- The a.e. formula for a single right translation. -/
theorem rightTranslation_apply_ae (g : Γ) (f : GroupL2 Γ) :
    (rightTranslation g f : Γ → ℂ) =ᵐ[Measure.count] fun x => f (x * g) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right Measure.count g)

/-- Composition has the order dictated by the right-translation convention. -/
theorem rightTranslation_mul (g h : Γ) (f : GroupL2 Γ) :
    rightTranslation g (rightTranslation h f) = rightTranslation (g * h) f := by
  apply Lp.ext
  have hcomp := (measurePreserving_mul_right Measure.count g).quasiMeasurePreserving.ae
    (rightTranslation_apply_ae h f)
  filter_upwards [rightTranslation_apply_ae g (rightTranslation h f), hcomp,
    rightTranslation_apply_ae (g * h) f] with x hx hy hz
  rw [hx, hy, hz, mul_assoc]

/-- Translation by the identity acts as the identity. -/
theorem rightTranslation_one (f : GroupL2 Γ) : rightTranslation (1 : Γ) f = f := by
  apply Lp.ext
  simpa only [mul_one] using rightTranslation_apply_ae (1 : Γ) f

/-- The adjoint of right translation by g is right translation by g⁻¹. -/
theorem rightTranslation_adjoint (g : Γ) :
    (rightTranslation g).toContinuousLinearMap.adjoint =
      (rightTranslation g⁻¹).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (rightTranslation g h) f = inner ℂ h (rightTranslation g⁻¹ f)
  have hi : rightTranslation g (rightTranslation g⁻¹ f) = f := by
    rw [rightTranslation_mul, mul_inv_cancel, rightTranslation_one]
  calc
    inner ℂ (rightTranslation g h) f =
        inner ℂ (rightTranslation g h) (rightTranslation g (rightTranslation g⁻¹ f)) := by rw [hi]
    _ = inner ℂ h (rightTranslation g⁻¹ f) := (rightTranslation g).inner_map_map _ _

/-- The adjoint formula, with the original jump labels retained. -/
theorem rightMarkov_adjoint (s : Finset Γ) (μ : Γ → ℝ) :
    (rightMarkov s μ).adjoint =
      ∑ g ∈ s, (μ g : ℂ) • (rightTranslation g⁻¹).toContinuousLinearMap := by
  simp only [rightMarkov, map_sum, map_smulₛₗ, rightTranslation_adjoint,
    Complex.conj_ofReal]

/-- Reindexing identifies P* with the Markov operator for μ̌(g)=μ(g⁻¹). -/
theorem rightMarkov_adjoint_eq_reflected (s : Finset Γ) (μ : Γ → ℝ) :
    (rightMarkov s μ).adjoint =
      rightMarkov (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) := by
  rw [rightMarkov_adjoint, rightMarkov, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, inv_inv]

/-- Pointwise form of the adjoint on counting-measure L². -/
theorem rightMarkov_adjoint_apply_ae (s : Finset Γ) (μ : Γ → ℝ) (f : GroupL2 Γ) :
    ((rightMarkov s μ).adjoint f : Γ → ℂ) =ᵐ[Measure.count]
      fun x => ∑ g ∈ s, (μ g : ℂ) * f (x * g⁻¹) := by
  rw [rightMarkov_adjoint_eq_reflected]
  simpa only [Finset.sum_map, Function.Embedding.coeFn_mk, inv_inv] using
    rightMarkov_apply_ae (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) f

end Singularity
