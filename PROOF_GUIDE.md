# Guide to the complete formal proof

## Final statements

`Singularity/FuchsianSingularity.lean` contains:

- `fuchsian_hittingMeasure_singular`: visual singularity.
- `fuchsian_hittingMeasure_singular_lebesgue`: real-chart Lebesgue singularity.
- `fuchsian_hittingLaw_singular`: any almost-sure geometric limit version.
- `fuchsian_randomWalk_converges_and_hittingMeasure_singular`: convergence
  and singularity together.

The hypotheses are a discrete nonelementary subgroup of PSL(2, ℝ) and a
finite positive probability support generating it as a semigroup. Neither
symmetry nor finite covolume is required. Lean's printed types are in
`THEOREM_STATEMENTS.txt`.

## The Dirichlet-end argument

Fix a basepoint z. The closed Dirichlet cell is

    D(z) = {w in H : d(w,z) <= d(w,gz) for every g in Γ}.

Discreteness makes the orbit locally finite, including finite stabilizer
multiplicities. Every point has a nearest orbit point, and therefore a
translate in D(z). A bounded D(z) gives a compact ball covering the quotient,
so the quotient is compact. `ProjectiveDirichletCell` proves these facts
without assuming trivial stabilizers.

For a noncompact quotient, choose w_n in D(z) with d(w_n,z)>n. Compactness
of the sphere gives a convergent subsequence. Its limit cannot be interior,
where distances would remain bounded. Thus it approaches an ideal point p.
This is `exists_ideal_dirichlet_sequence_of_noncompact`.

Choose any B in SL(2, ℝ) taking infinity to p. The transformed sequence
approaches infinity and satisfies, for every g,

    d(B^-1 w_n, B^-1 z) <= d(B^-1 w_n, B^-1 g z).

These comparisons imply

    Im(B^-1 g z) <= Im(B^-1 z)   for every g in Γ.

To see this, if v is higher than u then the hyperbolic half-plane
`d(w,u) <= d(w,v)` is bounded in the ordinary complex plane. The hyperbolic
cosine formula rearranges to

    (Im(v)-Im(u)) |w|^2 <= 2 A Re(w) + C,

where A,C depend only on u,v. The positive quadratic coefficient bounds
|w|, so the closure cannot contain infinity. `DirichletHeightBound` proves
this estimate, and `ProjectiveDirichletEnds` applies it to the cell sequence.
There is no finite-sidedness or surface-classification hypothesis.

## From one endpoint to finite separators

`projectiveBoundedHeightEndpoints Γ z` consists of ideal points at which
every infinity chart has bounded orbit height. `BoundedHeightEndpoints`
proves this set is group-invariant: translating the endpoint changes the
chart and reindexes the orbit.

`BoundaryOrbitMinimality` proves that the closure of any boundary orbit
contains the ideal limit set. When that limit set is full, the orbit of the
Dirichlet endpoint is dense.

Choose two distinct usable endpoints, and a chart B taking infinity and
zero to them. For a transformed orbit point x+iy the two bounds give
constants C,D>0 such that

    y <= C,               y/(x^2+y^2) <= D.

Inside the strip |x|/y<=R this implies

    1/(D(R^2+1)) <= y <= C,               |x| <= R C.

The strip lies in a compact interior rectangle and contains only finitely
many group vertices. Since a finite support has bounded jump length, a
finite enlargement contains every starting vertex of a supported exit
from the negative chart half-plane. `BoundedHeightSeparators` proves this.

Density lets the negative boundary arc fit inside any prescribed neighborhood
of an ideal point (`ShrinkingBoundaryCharts`). A convergent path starting
inside that half-plane and ending outside its boundary arc must hit the
finite exit set. The actual entrance identities convert this into deficit
compactness. `FuchsianDirichletDeficit` carries out the entire construction.

## Analytic assembly

`FuchsianSingularityFromDeficitCompactness` takes this geometric property and
proves singularity. It assembles common shadows, positive mass estimates,
logarithmic-cocycle estimates, finite corrections, and path coverage for the
actual hitting law. Hypothetical nonsingularity then gives a uniform Green
comparison by the checked cocycle-rigidity argument.

`FuchsianGreenRigidityReduction` turns the Green upper bound into orbit
quasiconvexity. `FuchsianQuasiconvexSingularity` gives the contradiction. That
result uses the proved visual-null/full-boundary dichotomy for quasiconvex
orbits and the cocompact theorem. These inputs are local Lean proofs.

## Other cases

For a proper ideal limit set, charts at ordinary boundary points have orbit
closures avoiding infinity and therefore bounded height. Its complement is
dense by boundary-orbit minimality. The same finite-separator mechanism
applies in `FuchsianCuspOrProperLimitSingularity`.

For a compact quotient, `FuchsianCocompactSingularity` uses the periodic-strip
proof: actual Martin and Naïm kernels, invariant currents, nonsymmetric
stable-product comparison, and a Fourier contradiction between finite
lattice translates and injective Liouville convolution. The separately
delivered cocompact folder has its own focused proof guide.

These three cases exhaust the theorem. The classification of finitely
generated parabolic-free Fuchsian groups is not required.

## Reproducibility

After obtaining the pinned dependencies, run `python3 verify.py`. It checks
local imports, builds the project, audits transitive axioms for every named
theorem and definition, and prints the final statements. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted.

`SOURCE_MANIFEST.json` identifies checked sources and configuration by hash.
`VERIFICATION.txt` contains the successful build and audit output. The source
ZIP excludes machine-specific compiled files and dependency caches.
