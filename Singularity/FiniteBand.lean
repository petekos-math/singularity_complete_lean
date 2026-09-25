import Singularity.FrequencyKernel
import Singularity.WeightedCauchySchwarz
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Packing a vector field into finitely many frequency bands

The half-open bands have width q. A unit vector field on [0,q) is packed into
one scalar function. Its squared L² norm is exactly q, so it is nonzero.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Singularity

/-- The l-th coordinate, restricted to the base cell and translated to band l. -/
def bandPiece {d : ℕ} (q : ℝ) (v : ℝ → EuclideanSpace ℂ (Fin d))
    (l : Fin d) (t : ℝ) : ℂ :=
  (Ico 0 q).indicator (fun ω => v ω l) (t - (l : ℕ) * q)

/-- The scalar function obtained by packing the coordinates into adjacent bands. -/
def finiteBand {d : ℕ} (q : ℝ) (v : ℝ → EuclideanSpace ℂ (Fin d)) (t : ℝ) : ℂ :=
  ∑ l, bandPiece q v l t

/-- A frequency belongs to at most one of the half-open lattice cells. -/
theorem band_index_unique {q : ℝ} (hq : 0 < q) {t : ℝ} {l m : ℕ}
    (hl : t - l * q ∈ Ico 0 q) (hm : t - m * q ∈ Ico 0 q) : l = m := by
  rcases lt_trichotomy l m with h | h | h
  · have hn : (l : ℝ) + 1 ≤ m := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_right hn hq.le
    nlinarith [hl.2, hm.1]
  · exact h
  · have hn : (m : ℝ) + 1 ≤ l := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_right hn hq.le
    nlinarith [hm.2, hl.1]

/-- On band l, the scalar function recovers coordinate l of the vector field. -/
theorem finiteBand_on_cell {d : ℕ} {q : ℝ} (hq : 0 < q)
    (v : ℝ → EuclideanSpace ℂ (Fin d)) (l : Fin d) {ω : ℝ}
    (hω : ω ∈ Ico 0 q) : finiteBand q v (ω + (l : ℕ) * q) = v ω l := by
  classical
  unfold finiteBand
  rw [Finset.sum_eq_single l]
  · simp [bandPiece, hω]
  · intro m _ hml
    apply indicator_of_notMem
    intro hm
    have hl : ω + (l : ℕ) * q - (l : ℕ) * q ∈ Ico 0 q := by simpa using hω
    exact hml (Fin.ext (band_index_unique hq hm hl))
  · simp

/-- Measurability of each packed coordinate. -/
theorem bandPiece_measurable {d : ℕ} (q : ℝ) {v : ℝ → EuclideanSpace ℂ (Fin d)}
    (hv : Measurable v) (l : Fin d) : Measurable (bandPiece q v l) := by
  exact (((PiLp.continuous_apply 2 (fun _ : Fin d => ℂ) l).measurable.comp hv).indicator
    measurableSet_Ico).comp (measurable_id.sub measurable_const)

/-- A measurable unit field gives square-integrable coordinate pieces. -/
theorem bandPiece_memLp {d : ℕ} (q : ℝ) {v : ℝ → EuclideanSpace ℂ (Fin d)}
    (hv : Measurable v) (hnorm : ∀ ω, ‖v ω‖ = 1) (l : Fin d) :
    MemLp (bandPiece q v l) 2 volume := by
  have hm : Measurable (fun ω => v ω l) :=
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℂ) l).measurable.comp hv
  have hb : ∀ ω, ‖v ω l‖ ≤ 1 := fun ω => (PiLp.norm_apply_le (v ω) l).trans_eq (hnorm ω)
  have hf : MemLp (fun ω => v ω l) 2 (volume.restrict (Ico 0 q)) :=
    MemLp.of_bound hm.stronglyMeasurable.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb)
  have hi := (memLp_indicator_iff_restrict measurableSet_Ico).mpr hf
  exact hi.comp_measurePreserving (measurePreserving_sub_right volume ((l : ℕ) * q))

/-- The packed scalar function belongs to L². -/
theorem finiteBand_memLp {d : ℕ} (q : ℝ) {v : ℝ → EuclideanSpace ℂ (Fin d)}
    (hv : Measurable v) (hnorm : ∀ ω, ‖v ω‖ = 1) : MemLp (finiteBand q v) 2 volume :=
  memLp_finsetSum Finset.univ (fun l _ => bandPiece_memLp q hv hnorm l)

/-- Disjoint bands eliminate every cross term in the squared norm. -/
theorem finiteBand_norm_sq {d : ℕ} {q : ℝ} (hq : 0 < q)
    (v : ℝ → EuclideanSpace ℂ (Fin d)) (t : ℝ) :
    ‖finiteBand q v t‖ ^ 2 = ∑ l, ‖bandPiece q v l t‖ ^ 2 := by
  classical
  by_cases hex : ∃ l : Fin d, t - (l : ℕ) * q ∈ Ico 0 q
  · obtain ⟨l, hl⟩ := hex
    have hz : ∀ m : Fin d, m ≠ l → bandPiece q v m t = 0 := by
      intro m hml
      apply indicator_of_notMem
      intro hm
      exact hml (Fin.ext (band_index_unique hq hm hl))
    unfold finiteBand
    rw [Finset.sum_eq_single l (fun m _ hm => hz m hm) (by simp),
      Finset.sum_eq_single l (fun m _ hm => by rw [hz m hm]; simp) (by simp)]
  · have hz : ∀ l : Fin d, bandPiece q v l t = 0 := by
      intro l
      exact indicator_of_notMem (fun hl => hex ⟨l, hl⟩) _
    simp [finiteBand, hz]

/-- The squared mass of a translated piece is the squared mass of its base coordinate. -/
theorem integral_bandPiece_sq {d : ℕ} (q : ℝ)
    (v : ℝ → EuclideanSpace ℂ (Fin d)) (l : Fin d) :
    ∫ t, ‖bandPiece q v l t‖ ^ 2 = ∫ ω in Ico 0 q, ‖v ω l‖ ^ 2 := by
  unfold bandPiece
  rw [integral_sub_right_eq_self (fun t => ‖(Ico 0 q).indicator (fun ω => v ω l) t‖ ^ 2)]
  rw [← integral_indicator measurableSet_Ico]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    by_cases ht : t ∈ Ico 0 q <;> simp [ht])

/-- Packing preserves the sum of coordinate masses. -/
theorem finiteBand_integral_norm_sq {d : ℕ} {q : ℝ} (hq : 0 < q)
    {v : ℝ → EuclideanSpace ℂ (Fin d)} (hv : Measurable v)
    (hnorm : ∀ ω, ‖v ω‖ = 1) : ∫ t, ‖finiteBand q v t‖ ^ 2 = q := by
  have hpieces : ∀ l : Fin d, Integrable (fun t => ‖bandPiece q v l t‖ ^ 2) :=
    fun l => (bandPiece_memLp q hv hnorm l).integrable_norm_pow (by decide)
  have hcoords : ∀ l : Fin d, IntegrableOn (fun ω => ‖v ω l‖ ^ 2) (Ico 0 q) := by
    intro l
    have hm : Measurable (fun ω => v ω l) :=
      (PiLp.continuous_apply 2 (fun _ : Fin d => ℂ) l).measurable.comp hv
    have hf : MemLp (fun ω => v ω l) 2 (volume.restrict (Ico 0 q)) :=
      MemLp.of_bound hm.stronglyMeasurable.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun ω => (PiLp.norm_apply_le (v ω) l).trans_eq (hnorm ω)))
    exact hf.integrable_norm_pow (by decide)
  calc
    ∫ t, ‖finiteBand q v t‖ ^ 2 = ∫ t, ∑ l, ‖bandPiece q v l t‖ ^ 2 := by
      congr 1; funext t; exact finiteBand_norm_sq hq v t
    _ = ∑ l, ∫ t, ‖bandPiece q v l t‖ ^ 2 := integral_finsetSum _ (fun l _ => hpieces l)
    _ = ∑ l, ∫ ω in Ico 0 q, ‖v ω l‖ ^ 2 := by simp_rw [integral_bandPiece_sq]
    _ = ∫ ω in Ico 0 q, ∑ l, ‖v ω l‖ ^ 2 :=
      (integral_finsetSum _ (fun l _ => hcoords l)).symm
    _ = ∫ ω in Ico 0 q, (1 : ℝ) := by
      congr 1; funext ω; rw [← EuclideanSpace.norm_sq_eq, hnorm, one_pow]
    _ = q := by simp [hq.le]

/-- The actual scalar L² vector supplied by finite-band packing. -/
def finiteBandL2 {d : ℕ} (q : ℝ) {v : ℝ → EuclideanSpace ℂ (Fin d)}
    (hv : Measurable v) (hnorm : ∀ ω, ‖v ω‖ = 1) : RealLineL2 :=
  (finiteBand_memLp q hv hnorm).toLp (finiteBand q v)

/-- Its exact norm certifies nontriviality without a pointwise-to-a.e. shortcut. -/
theorem finiteBandL2_norm_sq {d : ℕ} {q : ℝ} (hq : 0 < q)
    {v : ℝ → EuclideanSpace ℂ (Fin d)} (hv : Measurable v) (hnorm : ∀ ω, ‖v ω‖ = 1) :
    ‖finiteBandL2 q hv hnorm‖ ^ 2 = q := by
  rw [finiteBandL2, toL2_norm_sq]
  exact finiteBand_integral_norm_sq hq hv hnorm

/-- Positive band width gives a nonzero L² function. -/
theorem finiteBandL2_ne_zero {d : ℕ} {q : ℝ} (hq : 0 < q)
    {v : ℝ → EuclideanSpace ℂ (Fin d)} (hv : Measurable v) (hnorm : ∀ ω, ‖v ω‖ = 1) :
    finiteBandL2 q hv hnorm ≠ 0 := by
  intro h
  have hh := finiteBandL2_norm_sq hq hv hnorm
  rw [h, norm_zero, zero_pow (by decide)] at hh
  exact hq.ne' hh.symm

end Singularity
