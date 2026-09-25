import Singularity.ShearContraction
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Unimodularity of SL(2,ℝ)

The group is perfect, so its modular character is trivial. Therefore its
regular left Haar measures are also right invariant. The compactness and
Polish-space instances are obtained from the closed determinant-one locus.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups

namespace Singularity

theorem slTwo_locallyCompactSpace : LocallyCompactSpace SL(2, ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

theorem slTwo_polishSpace : PolishSpace SL(2, ℝ) := by
  let : PolishSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace

/-- Every character into a commutative monoid is trivial on SL(2,ℝ). -/
theorem slTwo_character_eq_one {C : Type*} [CommMonoid C]
    (f : SL(2, ℝ) →* C) (g : SL(2, ℝ)) : f g = 1 := by
  have hp : commutator SL(2, ℝ) = ⊤ :=
    Matrix.SL2.commutator_eq_top (a := (2 : ℝ)) (by norm_num) (by norm_num)
  have hk := Abelianization.commutator_subset_ker f.toHomUnits
  rw [hp] at hk
  have hg : f.toHomUnits g = 1 := hk (Subgroup.mem_top g)
  exact congrArg (fun u : Cˣ => (u : C)) hg

/-- The actual modular character is identically one. -/
theorem slTwo_modularCharacter_eq_one (g : SL(2, ℝ)) :
    letI := slTwo_locallyCompactSpace
    modularCharacterFun g = 1 := by
  let := slTwo_locallyCompactSpace
  exact slTwo_character_eq_one modularCharacter g

/-- A regular left Haar measure on SL(2,ℝ) is also right invariant. -/
theorem slTwo_haar_rightInvariant [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν] [ν.InnerRegular] : ν.IsMulRightInvariant := by
  let := slTwo_locallyCompactSpace
  refine ⟨fun g => ?_⟩
  rw [map_right_mul_eq_modularCharacterFun_smul ν g, slTwo_modularCharacter_eq_one, one_smul]

end Singularity
