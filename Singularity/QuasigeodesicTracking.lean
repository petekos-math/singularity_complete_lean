import Singularity.QuasigeodesicEnvelope
import Singularity.HyperbolicQuasiconvex

/-!
# Geodesic segments lie uniformly close to finite quasigeodesics

The proof uses exponential decay in disk coordinates and requires no abstract
Morse lemma. Only the direction needed for orbit quasiconvexity is asserted.
-/

noncomputable section
open scoped Classical BigOperators MatrixGroups UpperHalfPlane

namespace Singularity

/-- A uniform tracking radius; its size is irrelevant to quasiconvexity. -/
def quasigeodesicTrackingRadius (a b L : ℝ) : ℝ :=
  max 2 (2 * Real.log (16 * Real.exp L * Real.exp (b / 4) * latticeEnvelopeBound (a / 4)))

/-- The segment between the endpoints of a linearly separated bounded-step
chain passes uniformly near one of its vertices, first in the chart centered at i. -/
theorem quasigeodesic_near_I (p : ℕ → ℍ) (N : ℕ) (a b L : ℝ)
    (ha : 0 < a)
    (hstep : ∀ k < N, dist (p k) (p (k + 1)) ≤ L)
    (hlower : ∀ i ≤ N, ∀ j ≤ N,
      a * |(i : ℝ) - (j : ℝ)| - b ≤ dist (p i) (p j))
    (hsegment : dist (p 0) UpperHalfPlane.I + dist UpperHalfPlane.I (p N) = dist (p 0) (p N)) :
    ∃ m ≤ N, dist UpperHalfPlane.I (p m) ≤ quasigeodesicTrackingRadius a b L := by
  by_cases hd : 2 ≤ dist (p 0) (p N)
  · obtain ⟨m, hm, hmin⟩ := (Finset.range (N + 1)).exists_min_image
      (fun k => dist UpperHalfPlane.I (p k)) ⟨0, by simp⟩
    have hmN : m ≤ N := by have := Finset.mem_range.mp hm; omega
    have henv := cayley_quasigeodesic_envelope p N m a b L ha hstep
      (fun k hk => hmin k (Finset.mem_range.mpr (by omega)))
      (fun k hk => hlower k (by omega) m hmN)
    have hsep := halfPlaneCayley_dist_lower_of_excess (p 0) (p N) 0 hd (by
      rw [dist_comm (p N) UpperHalfPlane.I]
      linarith)
    have hbound : (1 : ℝ) / 4 ≤ 4 * Real.exp L *
        (Real.exp (-dist UpperHalfPlane.I (p m) / 2 + b / 4) * latticeEnvelopeBound (a / 4)) := by
      simpa using hsep.trans henv
    have hmultiply := mul_le_mul_of_nonneg_right hbound
      (show 0 ≤ 4 * Real.exp (dist UpperHalfPlane.I (p m) / 2) by positivity)
    have hexp : Real.exp (-dist UpperHalfPlane.I (p m) / 2 + b / 4) *
        Real.exp (dist UpperHalfPlane.I (p m) / 2) = Real.exp (b / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have he : Real.exp (dist UpperHalfPlane.I (p m) / 2) ≤
        16 * Real.exp L * Real.exp (b / 4) * latticeEnvelopeBound (a / 4) := by
      calc
        _ = (1 / 4 : ℝ) * (4 * Real.exp (dist UpperHalfPlane.I (p m) / 2)) := by ring
        _ ≤ _ := hmultiply.trans_eq (by
          calc
            _ = 16 * Real.exp L *
                (Real.exp (-dist UpperHalfPlane.I (p m) / 2 + b / 4) *
                Real.exp (dist UpperHalfPlane.I (p m) / 2)) * latticeEnvelopeBound (a / 4) := by ring
            _ = _ := by rw [hexp])
    have hlog := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp] at hlog
    refine ⟨m, hmN, (show dist UpperHalfPlane.I (p m) ≤
      2 * Real.log (16 * Real.exp L * Real.exp (b / 4) * latticeEnvelopeBound (a / 4)) by linarith).trans ?_⟩
    exact le_max_right _ _
  · refine ⟨0, Nat.zero_le _, ?_⟩
    have hsmall : dist UpperHalfPlane.I (p 0) ≤ 2 := by
      rw [dist_comm UpperHalfPlane.I (p 0)]
      linarith [dist_nonneg (x := UpperHalfPlane.I) (y := p N)]
    exact hsmall.trans (le_max_left _ _)

/-- Every point on the geodesic segment joining the endpoints is uniformly
close to a vertex of the finite quasigeodesic. -/
theorem quasigeodesic_segment_tracking (p : ℕ → ℍ) (N : ℕ) (a b L : ℝ)
    (ha : 0 < a)
    (hstep : ∀ k < N, dist (p k) (p (k + 1)) ≤ L)
    (hlower : ∀ i ≤ N, ∀ j ≤ N,
      a * |(i : ℝ) - (j : ℝ)| - b ≤ dist (p i) (p j))
    (o : ℍ) (hsegment : dist (p 0) o + dist o (p N) = dist (p 0) (p N)) :
    ∃ m ≤ N, dist o (p m) ≤ quasigeodesicTrackingRadius a b L := by
  let B := o.toSL2R
  let q : ℕ → ℍ := fun k => B⁻¹ • p k
  have hdist (i j : ℕ) : dist (q i) (q j) = dist (p i) (p j) := dist_smul _ _ _
  have hcenter (k : ℕ) : dist UpperHalfPlane.I (q k) = dist o (p k) := by
    rw [← dist_smul B UpperHalfPlane.I (q k)]
    simp only [q, B, smul_inv_smul, UpperHalfPlane.toSL2R_smul_I]
  obtain ⟨m, hm, hd⟩ := quasigeodesic_near_I q N a b L ha
    (fun k hk => by rw [hdist]; exact hstep k hk)
    (fun i hi j hj => by rw [hdist]; exact hlower i hi j hj) (by
      rw [dist_comm (q 0) UpperHalfPlane.I, hcenter, hcenter, hdist]
      simpa only [dist_comm o (p 0)] using hsegment)
  exact ⟨m, hm, by simpa only [hcenter] using hd⟩

/-- A set connected by uniformly linearly separated bounded-step chains is
quasiconvex, with an explicit uniform radius. -/
theorem hyperbolicQuasiconvex_of_chains (S : Set ℍ) (a b L : ℝ) (ha : 0 < a)
    (hchains : ∀ x ∈ S, ∀ y ∈ S, ∃ (N : ℕ) (p : ℕ → ℍ),
      p 0 = x ∧ p N = y ∧ (∀ k ≤ N, p k ∈ S) ∧
      (∀ k < N, dist (p k) (p (k + 1)) ≤ L) ∧
      (∀ i ≤ N, ∀ j ≤ N, a * |(i : ℝ) - (j : ℝ)| - b ≤ dist (p i) (p j))) :
    HyperbolicQuasiconvex S (quasigeodesicTrackingRadius a b L) := by
  intro x hx y hy o ho
  obtain ⟨N, p, hp0, hpN, hmem, hstep, hlower⟩ := hchains x hx y hy
  obtain ⟨m, hm, hd⟩ := quasigeodesic_segment_tracking p N a b L ha hstep hlower o
    (by simpa only [hp0, hpN] using ho)
  exact ⟨p m, hmem m hm, hd⟩

end Singularity
