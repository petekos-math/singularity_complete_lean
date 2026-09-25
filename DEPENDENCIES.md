# Dependencies and scope of the completed formal theorem

The entry point is `Singularity.fuchsian_hittingMeasure_singular`, in
`Singularity/FuchsianSingularity.lean`. Its mathematical inputs are:

- A subgroup Γ of Mathlib's PSL(2, ℝ), discrete in its induced topology.
- Nonelementarity, defined by absence of finite geometric orbits.
- A finite set of increments with positive weights summing to one.
- Generation of Γ as a semigroup by those increments.
- An arbitrary basepoint in the hyperbolic upper half-plane.

The measurable-space and measurable-singleton instances provide the discrete
random-walk formalism. No compactness, finite-covolume, symmetry, spectral-gap,
boundary identification, or analytic-rigidity hypothesis remains in the final
statement.

## Logical foundations

The transitive audit permits only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. It rejects `sorryAx` and every additional
axiom. No `sorry`, `admit`, `native_decide`, or custom axiom is used. Lean and
Mathlib are pinned by the toolchain and dependency lockfiles.

## Identification of the measure

`ProjectiveHittingMeasure` defines the law of a measurable limit selector
for the original projective random walk. `FuchsianHittingMeasure` proves
almost-sure geometric convergence, probability normalization, stationarity,
and independence of the almost-sure choice of the limit. The conclusion
thus concerns the actual hitting measure. The final module also proves the
result for any other almost-sure limit map.

## Proof branches

1. **Compact quotient:** `FuchsianCocompactSingularity` uses the proved Naïm
   current, stable-product comparison, and periodic-strip Fourier argument,
   including the nonsymmetric one-sided step.
2. **Proper ideal limit set:** `FuchsianCuspOrProperLimitSingularity` uses
   ordinary endpoints to obtain finite exit sets and deficit compactness.
3. **Noncompact quotient, full limit set:** `ProjectiveDirichletCell` and
   `ProjectiveDirichletEnds` produce an ideal Dirichlet endpoint.
   `DirichletHeightBound` bounds orbit height there. `BoundedHeightEndpoints`
   proves invariance and density; `BoundedHeightSeparators` proves finite
   exit sets; `FuchsianDirichletDeficit` supplies deficit compactness.

Both noncompact branches feed the proved theorem
`fuchsian_hittingMeasure_singular_of_deficit_compactness`. It assembles shadow
estimates and cocycle rigidity, obtains a Green upper comparison, and applies
the quasiconvex-orbit singularity theorem. These are local Lean proofs, not
unproved external theorem assumptions.

## Superseded structural route

The classification statement that a finitely generated discrete first-kind
group without parabolics is cocompact has not been formalized. The final proof
bypasses it by handling the noncompact full-limit-set case directly.
`FuchsianFirstKindReduction` retains the old conditional reduction for
reference; that input is absent from the final theorem.

The completed scope is finite support with semigroup generation. No extension
to arbitrary infinite-support laws or generation only as a group is asserted.
