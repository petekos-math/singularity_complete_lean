import Singularity.NaimSubsequence
import Singularity.MartinAction

/-!
# Covariance of finite and limiting normalized Green quotients

Left invariance of the actual Green kernel gives the precise two-factor
transformation rule. The rule passes to any existing limit represented by
forward and reflected Martin-boundary kernels. Existence of a full geometric
Naïm limit and construction of invariant measures are not asserted here.
-/

noncomputable section
open Filter
open scoped Topology

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ a ∈ s, 0 < μ a)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

include hpos hgen hgap in
/-- Exact covariance of the finite normalized Green quotient under simultaneous left translation. -/
theorem finiteNaimQuotient_translate (o g x y : Γ) :
    finiteNaimQuotient s μ o (g * x) (g * y) = finiteNaimQuotient s μ o x y /
      (reverseMartinQuotient s μ o (g⁻¹ * o) x * martinQuotient s μ o (g⁻¹ * o) y) := by
  have hxy := walkGreen_left s μ g x y
  have hxo := walkGreen_left s μ g x (g⁻¹ * o)
  have hoy := walkGreen_left s μ g (g⁻¹ * o) y
  simp only [mul_inv_cancel_left] at hxo hoy
  simp only [finiteNaimQuotient, reverseMartinQuotient, martinQuotient, hxy, hxo, hoy]
  have h1 := walkGreen_ne_zero s μ hpos hgen hgap x o
  have h2 := walkGreen_ne_zero s μ hpos hgen hgap o y
  have h3 := walkGreen_ne_zero s μ hpos hgen hgap x (g⁻¹ * o)
  have h4 := walkGreen_ne_zero s μ hpos hgen hgap (g⁻¹ * o) y
  field_simp

include hpos hgen hgap in
/-- When the original quotient and Martin coordinates converge, the translated
quotient converges with the exact forward/reflected cocycle factors. -/
theorem naim_limit_translate {α : Type*} {l : Filter α}
    (o g : Γ) (x y : α → Γ) (θ : ℝ)
    (ξ : martinBoundary (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹) o)
    (η : martinBoundary s μ o)
    (hθ : Tendsto (fun n => finiteNaimQuotient s μ o (x n) (y n)) l (𝓝 θ))
    (hm : ∀ z, Tendsto (fun n => reverseMartinQuotient s μ o z (x n)) l
      (𝓝 (martinBoundaryKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹) o z ξ)))
    (hp : ∀ z, Tendsto (fun n => martinQuotient s μ o z (y n)) l
      (𝓝 (martinBoundaryKernel s μ o z η))) :
    Tendsto (fun n => finiteNaimQuotient s μ o (g * x n) (g * y n)) l
      (𝓝 (θ / (martinBoundaryCocycle (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹) o g ξ *
        martinBoundaryCocycle s μ o g η))) := by
  have hcm := martinBoundaryCocycle_pos (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹)
    (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
    (reflectedMarkov_spectral_gap s μ hgap) o g ξ
  have hcp := martinBoundaryCocycle_pos s μ hpos hgen hgap o g η
  have ht := hθ.div ((hm (g⁻¹ * o)).mul (hp (g⁻¹ * o))) (ne_of_gt (mul_pos hcm hcp))
  apply ht.congr'
  exact Eventually.of_forall (fun n => (finiteNaimQuotient_translate s μ hpos hgen hgap o g (x n) (y n)).symm)

end Singularity
