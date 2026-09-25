import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The block inverse identity

Use `D = I_B - P_BB`, `X = G_AA`, `Y = G_AB`, `Z = G_BA`,
`W = G_BB`, `M = X⁻¹`, and `V = D⁻¹`. The two block equations here are
the lower row of `(I-P)G = I`. No finite-dimensional assumption is made.
-/

namespace Singularity

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The lower-right Schur-complement identity in bounded-operator form. -/
theorem block_inverse_identity
    (C : E →L[𝕜] F) (D V : F →L[𝕜] F)
    (X M : E →L[𝕜] E) (Y : F →L[𝕜] E)
    (Z : E →L[𝕜] F) (W : F →L[𝕜] F)
    (hfirst : ∀ x, C (X x) + D (Z x) = 0)
    (hsecond : ∀ y, C (Y y) + D (W y) = y)
    (hXM : ∀ x, X (M x) = x)
    (hVD : ∀ y, V (D y) = y) :
    W - Z.comp (M.comp Y) = V := by
  ext y
  change W y - Z (M (Y y)) = V y
  have hz := hfirst (M (Y y))
  rw [hXM] at hz
  have hd : D (W y - Z (M (Y y))) = y := by
    rw [map_sub]
    have hz' : D (Z (M (Y y))) = -C (Y y) := eq_neg_of_add_eq_zero_right hz
    rw [hz', sub_neg_eq_add, add_comm]
    exact hsecond y
  have hv := congrArg V hd
  rw [hVD] at hv
  exact hv

end Singularity
