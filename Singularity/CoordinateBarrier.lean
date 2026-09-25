import Singularity.RelativeBoundaryComparison
import Singularity.StripSeparation

/-!
# Bounded-jump coordinate barriers

A coordinate changing by at most L in one jump cannot cross a closed layer
of width L without visiting it. A layer separated from a lower stopping set
also intercepts every first entrance into that set, including its final jump.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- A closed layer of one-jump width separates its strict opposite sides. -/
theorem bounded_coordinate_layer_separates (s : Finset Γ) (h : Γ → ℝ) (L t : ℝ)
    (hL : 0 ≤ L)
    (hjump : ∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L)
    (D : Set Γ) (hcover : ∀ x, t ≤ h x → h x ≤ t + L → x ∈ D)
    (x y : Γ) (hx : t + L < h x) (hy : h y < t) :
    SeparatesJumpPaths s D x y := by
  apply separatesJumpPaths_of_invariant_side s D {z | t + L < h z}
    ?_ x y hx ?_
  · intro z g hg _hz hznext hzside
    change t + L < h z at hzside
    change t + L < h (z*g)
    have hb := (abs_le.mp (hjump z g hg)).1
    by_contra! hn
    exact hznext (hcover (z*g) (by linarith) hn)
  · change ¬ t + L < h y
    linarith

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]

/-- A layer with a one-jump gap from the stopping set intercepts all entrances
from its upper side. This proves that the direct last-exit remainder vanishes. -/
theorem firstEntrance_eq_zero_of_coordinate_barrier
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (h : Γ → ℝ) (L r t : ℝ) (hL : 0 ≤ L)
    (hjump : ∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L)
    (A B : Set Γ) (hA : ∀ a ∈ A, h a ≤ r)
    (hB : ∀ b, t ≤ h b → h b ≤ t + L → b ∈ B)
    (hmargin : r + L < t) (x : Γ) (hx : t + L < h x)
    {a : Γ} (ha : a ∈ A) : firstEntranceKernel s μ (A ∪ B) x a = 0 := by
  apply firstEntrance_eq_zero_of_predecessor_separators s μ hμ hmass hgap (A ∪ B)
    (Set.mem_union_left B ha) x
  · intro hxa
    have hax := hA a ha
    rw [hxa] at hx
    linarith
  · intro g hg
    apply bounded_coordinate_layer_separates s h L t hL hjump (A ∪ B)
      (fun b hb₁ hb₂ => Set.mem_union_right A (hB b hb₁ hb₂)) x (a*g⁻¹) hx
    have hb := (abs_le.mp (hjump (a*g⁻¹) g hg)).1
    simp only [inv_mul_cancel_right] at hb
    have hax := hA a ha
    linarith

/-- With the geometric interception proved, relative Green comparison on a
coordinate layer suffices for every nonnegative harmonic boundary datum. -/
theorem harmonic_comparison_of_coordinate_barrier
    (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
    (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (h : Γ → ℝ) (L r t : ℝ) (hL : 0 ≤ L)
    (hjump : ∀ x : Γ, ∀ g ∈ s, |h (x*g) - h x| ≤ L)
    (A B : Set Γ) (hA : ∀ a ∈ A, h a ≤ r)
    (hB : ∀ b, t ≤ h b → h b ≤ t + L → b ∈ B)
    (hmargin : r + L < t) (x o : Γ) (hx : t + L < h x) (ho : t + L < h o)
    (f : Γ → ℝ) (hf : MeasureTheory.MemLp (fun x => (f x : ℂ)) 2 MeasureTheory.Measure.count)
    (hharm : ∀ x, x ∉ A → f x = ∑ g ∈ s, μ g * f (x*g))
    (hboundary : ∀ a ∈ A, 0 ≤ f a) (lower upper : ℝ)
    (hcompare : ∀ b ∈ B \ A,
      lower * killedGreen s μ A o b ≤ killedGreen s μ A x b ∧
      killedGreen s μ A x b ≤ upper * killedGreen s μ A o b) :
    lower * f o ≤ f x ∧ f x ≤ upper * f o := by
  apply harmonic_comparison_of_relativeGreen s μ hμ hmass hgap A B f hf hharm
    hboundary x o lower upper ?_ hcompare
  intro a ha
  exact ⟨firstEntrance_eq_zero_of_coordinate_barrier s μ hμ hmass hgap h L r t hL
      hjump A B hA hB hmargin x hx ha,
    firstEntrance_eq_zero_of_coordinate_barrier s μ hμ hmass hgap h L r t hL
      hjump A B hA hB hmargin o ho ha⟩

end Singularity
