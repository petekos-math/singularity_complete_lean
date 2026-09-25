import Singularity.GeometricStrip
import Singularity.OrbitGreenBoundary

/-!
# Green factorization through the constructed geometric separator

These statements apply the already proved Green factorization to the actual
finite-jump strip. Neither path separation nor a strip enumeration is assumed.
The operator spectral gap remains an explicit unresolved input.
-/

noncomputable section
open MeasureTheory Set
open scoped MatrixGroups UpperHalfPlane

namespace Singularity

variable (Γ : Subgroup SL(2, ℝ)) [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
  (z : ℍ) (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

/-- The Green pairing holds for the constructed geometric strip. -/
theorem geometricStrip_Green_pairing (x y : Γ)
    (hx : (x • z).re < 0) (hy : 0 ≤ (y • z).re) :
    let A := finiteJumpStrip Γ z s
    (walkGreen s μ x y : ℂ) = inner ℂ
      (supportedRestriction A ((green (rightMarkov s μ)).adjoint (countingDelta x)))
      ((walkGreenCompression s μ hμ hmass hgap A).symm
        (supportedRestriction A (green (rightMarkov s μ) (countingDelta y)))) := by
  exact walkGreen_separator_pairing s μ hμ hmass hgap (finiteJumpStrip Γ z s) x y
    (finiteJumpStrip_separates Γ z s x y hx hy)

/-- The normalized pairing holds in the actual cyclic strip coordinates. -/
theorem geometricStrip_orbitGreen_pairing (a : Γ) {τ : ℝ}
    (ha : (a : SL(2, ℝ)) = dilationMatrix τ) (hτ : 0 < τ)
    (x y : Γ) (r c : ℝ) (hx : (x • z).re < 0) (hy : 0 ≤ (y • z).re) :
    let e := stripOrbitEquiv Γ a ha hτ z (jumpStripRadius (finiteJumpLengthBound Γ z s))
    (walkGreen s μ x y : ℂ) / ((r : ℂ) * (c : ℂ)) = inner ℂ
      (orbitGreenRow s μ e x r)
      (orbitGreenInverse s μ hμ hmass hgap e (orbitGreenColumn s μ e y c)) := by
  exact orbitGreen_separator_pairing s μ hμ hmass hgap
    (stripOrbitEquiv Γ a ha hτ z (jumpStripRadius (finiteJumpLengthBound Γ z s)))
    x y r c (finiteJumpStrip_separates Γ z s x y hx hy)

end Singularity
