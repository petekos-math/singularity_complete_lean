# Completion audit

The full finite-support, semigroup-generating singularity objective is proved
by `Singularity.fuchsian_hittingMeasure_singular`.

| Requirement | Checked evidence |
| --- | --- |
| Actual discrete subgroup of PSL(2, ℝ) | Printed final statement; `ProjectiveActions` descends the actual SL action. |
| Geometric nonelementarity | `ProjectiveNonelementary` excludes finite interior and boundary orbits. |
| Arbitrary finite admissible law, without symmetry | Final type: positive weights on a finite set, total one, semigroup closure equal to the group. |
| Actual right random walk | `walkPosition`, its product probability law, and `walkPosition_law`. |
| Actual boundary hitting probability | `projectiveHittingMeasure_probability` and `fuchsian_boundaryMap_tendsto`. |
| Singularity to visual and Lebesgue measures | The first two final declarations in `FuchsianSingularity`. |
| All covolumes | Final statement has no compactness/covolume premise; proof exhausts compact quotient, proper limit set, and noncompact full limit set. |
| No residual classification or rigidity hypothesis | Lean's printed final type contains only the stated group and probability assumptions. |
| No admitted proofs or extra axioms | Full transitive audit of 2,591 declarations permits only `propext`, `Classical.choice`, and `Quot.sound`. |
| Reproducible sources | 519 local modules, pinned toolchain and dependencies, `verify.py`, and source hashes in `SOURCE_MANIFEST.json`. |
| Separately requested cocompact folder | Previously verified independent `cocompact-proof` extraction remains available. |

The final build completed successfully with 4,471 jobs. The full audit
reported no additional axioms. Source hashes were compared with the files
before packaging. The earlier classification-based route is unnecessary;
its unproved structural implication is not used as a premise of the final
theorem.

The theorem keeps the agreed finite-support and semigroup-generation scope.
An infinite-support extension or weakening to group generation was not part
of this completed formal statement.
