import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Independence.InfinitePi

/-!
# Zero–one law for almost shift-invariant events

A measurable event in an independent sequence that is unchanged almost surely
by every finite shift has probability zero or one. Taking the limsup of its
shifted copies produces a genuine tail-measurable representative.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace

namespace Singularity

/-- A shifted measurable event uses only coordinates at or beyond the shift. -/
theorem shifted_event_measurable {S : Type*} [MeasurableSpace S]
    {E : Set (ℕ → S)} (hE : MeasurableSet E) (k n : ℕ) (hkn : k ≤ n) :
    MeasurableSet[⨆ i ≥ k, MeasurableSpace.comap (fun ω : ℕ → S => ω i)
      inferInstance] ((fun (ω : ℕ → S) i => ω (i + n)) ⁻¹' E) := by
  apply hE.preimage
  apply (@measurable_pi_iff (ℕ → S) ℕ (fun _ => S)
    (⨆ i ≥ k, MeasurableSpace.comap (fun ω : ℕ → S => ω i) inferInstance) _).mpr
  intro i
  apply Measurable.of_comap_le
  exact le_iSup_of_le (i + n) (le_iSup_of_le (by omega : k ≤ i + n) le_rfl)

/-- Limsup of shifted copies belongs to the coordinate tail sigma algebra. -/
theorem shifted_event_limsup_tail {S : Type*} [MeasurableSpace S]
    {E : Set (ℕ → S)} (hE : MeasurableSet E) :
    MeasurableSet[limsup (fun i => MeasurableSpace.comap
      (fun ω : ℕ → S => ω i) inferInstance) atTop]
      (limsup (fun n => (fun (ω : ℕ → S) i => ω (i + n)) ⁻¹' E) atTop) := by
  rw [limsup_eq_iInf_iSup_of_nat]
  apply measurableSet_iInf.mpr
  intro k
  rw [← limsup_nat_add (fun n => (fun (ω : ℕ → S) i => ω (i + n)) ⁻¹' E) k]
  exact @MeasurableSet.measurableSet_limsup (ℕ → S)
    (⨆ i ≥ k, MeasurableSpace.comap (fun ω : ℕ → S => ω i) inferInstance) _ (fun n => shifted_event_measurable hE k (n+k) (by omega))

/-- Independent coordinates force every almost shift-invariant event to have mass zero or one. -/
theorem independent_shift_event_zero_one {S : Type*} [MeasurableSpace S]
    (ν : Measure (ℕ → S))
    (hind : iIndepFun (fun n (ω : ℕ → S) => ω n) ν)
    {E : Set (ℕ → S)} (hE : MeasurableSet E)
    (hinv : ∀ n : ℕ, (fun (ω : ℕ → S) i => ω (i + n)) ⁻¹' E =ᵐ[ν] E) :
    ν E = 0 ∨ ν E = 1 := by
  let T := limsup (fun n => (fun (ω : ℕ → S) i => ω (i + n)) ⁻¹' E) atTop
  have hT : T =ᵐ[ν] E := by
    have hall := ae_all_iff.mpr (fun n => (hinv n).mem_iff)
    filter_upwards [hall] with ω hω
    apply propext
    simp only [T, limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion,
      mem_iInter, mem_iUnion, hω]
    constructor
    · intro h
      obtain ⟨n, _, hn⟩ := h 0
      exact hn
    · intro h k
      exact ⟨k, le_rfl, h⟩
  rw [← measure_congr hT]
  exact measure_zero_or_one_of_measurableSet_limsup_atTop
    (fun n => (measurable_pi_apply n).comap_le) hind (shifted_event_limsup_tail hE)

end Singularity
