import Singularity.InfiniteFirstEntrance
import Singularity.WalkPrefixTail
import Singularity.WalkBoundaryTimeCocycle

/-!
# Joint first-entrance and boundary probabilities

The first-step boundary relation and independence of prefix and future give
an exact first-entrance formula for boundary events. This is proved on the
actual infinite path space, without assuming a strong Markov theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal
namespace Singularity

variable {Γ B : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableSpace B] [MulAction Γ B] [MeasurableConstSMul Γ B]
  (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (b : (ℕ → s) → B) (hb : Measurable b)
  (hstep : ∀ᵐ ω ∂infiniteWalkLaw s μ hμ hmass,
    b ω = (ω 0 : Γ) • b (fun k => ω (k + 1)))

include hb hstep

/-- Boundary and first-entrance events factor at every deterministic time. -/
theorem walkFirstEntranceEvent_boundary_probability (A : Set Γ) (x a : Γ) (n : ℕ)
    {E : Set B} (hE : MeasurableSet E) :
    infiniteWalkLaw s μ hμ hmass (walkFirstEntranceEvent s A x a n ∩
      {ω | x • b ω ∈ E}) = ENNReal.ofReal (firstEntranceWeight s μ A n x a) *
        walkBoundaryLaw s μ hμ hmass b ((fun ξ : B => a • ξ) ⁻¹' E) := by
  let P := infiniteWalkLaw s μ hμ hmass
  let T : Set (WalkWord s n) :=
    {w | avoidsBefore s A n x w ∧ walkEndpoint s n x w = a ∧ a ∈ A}
  let V : Set (ℕ → s) := {ω | a • b ω ∈ E}
  have hV : MeasurableSet V := hE.preimage ((measurable_const_smul a).comp hb)
  have he : walkFirstEntranceEvent s A x a n ∩ {ω | x • b ω ∈ E} =ᵐ[P]
      walkFirstEntranceEvent s A x a n ∩ (fun ω k => ω (k + n)) ⁻¹' V := by
    filter_upwards [walkBoundaryMap_time_cocycle s μ hμ hmass b hstep n] with ω hω
    apply propext
    by_cases hent : ω ∈ walkFirstEntranceEvent s A x a n
    · have hp := (mem_walkFirstEntranceEvent s A x a n ω).mp hent
      have hx : x • b ω = a • b (fun k => ω (k + n)) := by
        rw [hω, ← mul_smul]
        have hpos : x * walkPosition s 1 n ω = a := by
          simpa only [mul_one] using (walkPosition_left s x 1 n ω).symm.trans (by simpa only [mul_one] using hp.2.1)
        rw [hpos]
      simp only [mem_inter_iff, hent, true_and, mem_ofPred_eq, mem_preimage, V, hx]
    · simp only [mem_inter_iff, hent, false_and]
  rw [measure_congr he]
  have hi := (infiniteWalkLaw_prefix_tail_independent s μ hμ hmass n).meas_inter
    ((show MeasurableSet T from trivial).preimage (comap_measurable (walkPrefix s n)))
    (hV.preimage (comap_measurable (fun (ω : ℕ → s) k => ω (k + n))))
  change P (walkFirstEntranceEvent s A x a n ∩ (fun ω k => ω (k + n)) ⁻¹' V) =
    P (walkFirstEntranceEvent s A x a n) * P ((fun ω k => ω (k + n)) ⁻¹' V) at hi
  rw [hi, walkFirstEntranceEvent_probability s μ hμ hmass,
    ← Measure.map_apply (by fun_prop) hV, infiniteWalkLaw_shift]
  congr 1
  exact (Measure.map_apply hb (hE.preimage (measurable_const_smul a))).symm

/-- Summing over the disjoint entrance times gives the full entrance formula
with the actual kernel F_A(x,a). -/
theorem walkFirstEntranceEver_boundary_probability [MeasurableMul Γ]
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    (A : Set Γ) (x a : Γ) {E : Set B} (hE : MeasurableSet E) :
    infiniteWalkLaw s μ hμ hmass (walkFirstEntranceEver s A x a ∩
      {ω | x • b ω ∈ E}) = ENNReal.ofReal (firstEntranceKernel s μ A x a) *
        walkBoundaryLaw s μ hμ hmass b ((fun ξ : B => a • ξ) ⁻¹' E) := by
  rw [walkFirstEntranceEver, iUnion_inter]
  have hm (n : ℕ) : MeasurableSet (walkFirstEntranceEvent s A x a n ∩ {ω | x • b ω ∈ E}) :=
    (measurableSet_walkFirstEntranceEvent s A x a n).inter
      (hE.preimage ((measurable_const_smul x).comp hb))
  rw [measure_iUnion (fun n m hnm =>
    (walkFirstEntranceEvent_disjoint s A x a hnm).mono inter_subset_left inter_subset_left) hm]
  simp only [walkFirstEntranceEvent_boundary_probability s μ hμ hmass b hb hstep A x a _ hE]
  rw [ENNReal.tsum_mul_right,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => firstEntranceWeight_nonneg s μ hμ A n x a)
      (firstEntranceWeight_summable s μ hμ hgap A x a)]
  rfl

end Singularity
