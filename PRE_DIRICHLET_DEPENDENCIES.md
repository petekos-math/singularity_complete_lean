> Historical snapshot before the final Dirichlet-end argument. See README.md for the current theorem.

# Remaining work for the full singularity theorem

The nonelementary `PSL(2, ℝ)` theorem is now proved for all quasiconvex orbits,
including cocompact and noncocompact cases, for every group containing a
parabolic, and for every proper ideal limit set, without symmetry. The projective group, original
walk law, and finite-orbit definition of nonelementarity are
included in the checked statement. The unrestricted theorem is not introduced
as an axiom or admitted proof.

## Current remaining obligation: first kind without parabolics

The required structural implication is now precisely:

```text
Γ discrete and nonelementary, finitely generated,
projectiveOrbitLimitSet Γ z = univ,
∀ g ∈ Γ, g is not parabolic
    ⇒ the hyperbolic orbit quotient is compact.
```

Finite generation is supplied by the original finite semigroup-generating
support. The implication itself remains unproved. `FuchsianFirstKindReduction`
checks the final assembly from it and proves that a putative nonsingular
example must have full limit set, no parabolics, and noncompact quotient.
It is not imported as an axiom, an admitted proof, or a hidden instance.

`FuchsianCuspOrProperLimitSingularity` now proves the remaining analytic
estimates outright when a parabolic exists or the ideal limit set is proper.
The endpoints used for finite strips may be parabolic fixed points or points
outside the limit set. At ordinary endpoints the compactified orbit closure
avoids the chart's infinity, giving a bounded complex orbit and hence a
height bound. At parabolic endpoints the discrete orbit-height theorem
applies. Both bounds yield compact interior rectangles and finite exit sets.

For a proper limit set, a boundary orbit starting outside it stays outside
and accumulates on the whole limit set, so its complement is dense. If a
parabolic exists, parabolic fixed points accumulate on the entire limit set.
Thus the union of parabolic and ordinary endpoints is dense in either case.
Shrinking charts prove deficit compactness and actual visual/Lebesgue
singularity. No visual-nullity assertion for a proper limit set is needed.

The detailed construction history below includes earlier, now superseded
interfaces; the structural implication in this section is the current
outstanding requirement for the full theorem.

## 1. The nonsymmetric one-sided conclusion — completed

`cocompact_hittingMeasure_singular_of_infinite_orbits` proves forward
singularity for every finite positive probability support generating the
cocompact group as a semigroup. It has no symmetry, spectral-gap, current,
chart, or density-bound assumption beyond the stated geometric hypotheses.

The former one-sided gap is closed by the following checked chain:

- Construct the actual positive continuous invariant Naïm current from the
  forward and reflected hitting measures, without visual absolute continuity.
- Lift it to the signed frame bundle, prove local finiteness, and descend it
  to a finite nonzero geodesic-flow-invariant quotient probability.
- Choose a measurable section whose first row depends only on the forward
  endpoint. Varying the backward endpoint at fixed transverse coordinates
  follows a contracting lower horocycle.
- Prove the Liouville frame lift has Haar measure class, and use Fubini to
  transfer its full stable basins to an arbitrary backward marginal with an
  absolutely continuous forward marginal. The off-diagonal restriction is
  handled explicitly, including endpoints at infinity.
- Identify the actual Naïm quotient probability with Haar using invariance
  and the integrals of continuous observables. Transfer this equality back
  to visual absolute continuity of both hitting marginals.
- Apply the zero–one law and the already checked two-sided Fourier
  contradiction to conclude forward singularity. Applying the result to
  the reflected walk also gives reflected singularity.

The final theorem is in `CocompactHittingSingularity.lean`; the one-sided
comparison is in `OneSidedNaimRigidity.lean`. No chart comparison remains an
unproved hypothesis of this cocompact conclusion.

## 2. The noncocompact cases

The original manuscript reduces these to Kim–Zimmer, *Rigidity for
Patterson–Sullivan systems with applications to random walks and entropy
rigidity*, [arXiv:2505.16556v3](https://arxiv.org/html/2505.16556v3),
Corollary 1.7 (proved as Corollary 12.2), using Theorem 1.9 (Theorem 12.1).
Its hypotheses include relative hyperbolicity of the abstract group and finite
superexponential moment. The manuscript supplies relative hyperbolicity via
the structure of finitely generated Fuchsian groups. Neither that structural
reduction nor the rigidity theorem has been formalized here.

The geometric consequences of quasiconvexity are now proved independently:

- `ParabolicOrbitHeight.lean` derives a positive nonzero displacement gap from
  proper discontinuity and bounds every orbit's height in shear coordinates.
- `ParabolicMidpoint.lean` constructs the exact metric midpoint between
  opposite translates and proves that its height grows with the parameter.
- `HyperbolicQuasiconvex.lean` defines metric-segment quasiconvexity and proves
  its invariance under isometries and the projective lift.
- `QuasiconvexParabolic.lean` proves that no orbit of a discrete projective
  group containing a parabolic can be quasiconvex. The finite-index
  free-subgroup hypothesis is unnecessary for this geometric obstruction.
- `FullIdealBoundary.lean` constructs ideal approach sequences and a universal
  triangle-excess bound using opposite Cayley boundary coordinates.
- `QuasiconvexFullBoundary.lean` uses those estimates to prove uniform density
  and an actual compact orbit quotient from quasiconvexity and full limit set.
- `FuchsianQuasiconvexReduction.lean` applies the completed cocompact theorem
  and states the remaining rigidity and limit-set premises explicitly.

The limit-set alternative is now proved for every quasiconvex orbit in
`QuasiconvexLimitSetDichotomy.lean`. The proof tracks vertical ideal approaches
using `VerticalRayExcess` and `QuasiconvexConical`, then applies the Poisson
concentration theorem proved from Lebesgue density and rescaling in
`DensityRescaling`, `BoundedDensityConcentration`, and `PoissonDensityPoint`.
`LimitSetDynamics` and `VisualPoissonOrbit` show that visual mass is constant
along the orbit and pass the concentration back to the fixed basepoint.
Closedness and full support yield the full-boundary conclusion.

`FuchsianQuasiconvexSingularity.lean` therefore proves singularity for every
discrete nonelementary group with a quasiconvex orbit. Its final reduction
`fuchsian_singularity_of_quasiconvex_rigidity` has a single remaining premise:
nonsingularity implies quasiconvexity. This is still a substantial unproved
analytic rigidity statement. No visual-nullity hypothesis remains in that
reduction. Applying the cited rigidity theorem would still require formalizing
its hypotheses, including the structural group reduction.

The Green-comparison-to-quasiconvexity step is now fully checked.
`QuasigeodesicEnvelope` sums exponentially decaying Cayley movements along a
finite chain with a linear distance lower bound. `QuasigeodesicTracking`
compares this with endpoint separation and proves that every point of the
endpoint segment stays near a chain vertex, with a radius independent of the
chain length. `WordGeodesics` constructs actual shortest word chains and
checks their subpath distance equality; `OrbitWordQuasiconvex` applies tracking
to the orbit. `GreenOrbitQuasiconvex` then uses the proved Green/word lower bound
to derive quasiconvexity from the one-sided radial estimate
`greenDistance(1,g) ≤ c * dist(z,g•z) + C`, with `c > 0`.

`FuchsianGreenRigidityReduction` connects this estimate to the completed
quasiconvex singularity theorem. Thus it is sufficient to prove that
nonsingularity implies this radial upper estimate. This remains an explicit,
unproved premise. No structural group theorem, relative-hyperbolicity theorem,
or abstract Morse lemma is assumed in the comparison-to-singularity part.
The external rigidity route still needs its own structural hypotheses proved.

The initial measure-theoretic part of that analytic step is now checked for
the original projective walk. `FuchsianHittingErgodicity` proves invariant
zero–one and nonsingularity implying visual absolute continuity without
compactness. `InvariantDensityCarrier` restricts the reference to an invariant
hitting-conull set on which the measures are equivalent; it does not establish
full visual equivalence. `StationaryLogCocycle` derives exact logarithmic
Radon–Nikodym cocycles and two directed Green-distance bounds by optional
stopping. `StationaryCocycleDomain` makes the identities simultaneous on an
exactly invariant conull set. `RadonNikodymCoboundary` proves the exact density
coboundary under a change of measure. `VisualLogCocycle` bounds the visual
cocycle by hyperbolic displacement, and `FuchsianLogCocycle` and
`FuchsianDensityCocycle` apply the results to the actual hitting law.

The visual part of the shadow estimates is now checked. `VisualShadows`
constructs transported open caps with two-sided exponential visual mass bounds.
`VisualShadowDensity` strengthens the upper bound to restricted measures, and
`VisualShadowCocycle` obtains a bounded visual cocycle error on inverse caps.
`VisualShadowSize` proves uniform fullness of inverse caps and vanishing mass
of caps with escaping centers. `FiniteMeasureAbsoluteContinuity` and
`AbsolutelyContinuousVisualShadows` transfer those two mass properties without
assuming bounded density. `FuchsianVisualShadows` applies them to the actual
nonsingular hitting law and retains the exact density coboundary in the
shadow cocycle estimate. The chosen caps have not been identified with
harmonic/Green shadows, and no equivariance of the chosen axes is assumed.

These statements do not bound the density uniformly. The conditional theorem
with an essentially bounded log density concludes a bound on the hitting
cocycle, not on Green distance. Deriving density control and the required
shadow/Green comparison in the noncocompact setting remains substantial work.
The cocompact Martin identification cannot fill this gap without additional
proof. The nonsingularity-to-Green-upper-bound premise remains unproved.

The measure-theoretic middle and end of the mixed-shadow route are now
formalized conditionally in `ShadowRigidityFromReturnCover`. Starting from a
common family with exponential mass and cocycle estimates, a sequence whose
mass ratio tends to a positive finite limit, and a finite corrected return
cover into a bounded-density window, it proves uniformly bounded magnitude
difference. `ShadowRatioRigidity` proves the sequence bound;
`ReturnCoverDensityRigidity` performs the density upgrade;
`LogDensityMeasureComparison` converts bounded log density to measure
comparison under explicit equivalence; `ShadowMagnitudeComparison` finishes
the uniform magnitude comparison. `CocycleShadowMeasure` and
`MixedShadowMeasure` prove the integral and intersection estimates supplying
the measure-theoretic shadow lemma. None of these theorems assumes its own
conclusion. The newer pathwise assembly below removes the differentiation
premises; common geometric shadow estimates remain substantial unproved inputs.

For the actual Fuchsian hitting law, `StationaryGreenMeasure` and
`FuchsianGreenShadows` now give the lower bound
`(1-epsilon) * exp(-greenDistance(1,g))` on sufficiently wide visual shadows
under nonsingularity. `FuchsianShadowCorrections` supplies the uniform cocycle
difference bound for any finite correction set. The lower shadow estimate
cannot be used as the missing upper estimate. `FuchsianGreenShadows` checks a
sufficient interface using an upper Green shadow estimate and one-sided
visual domination by the hitting law; neither follows from the proved lower
estimate. In the mixed-shadow route, the common harmonic/Green family and
its uniform mass and exceptional-set estimates remain to be established.
The local cocycle estimates are now supplied by a concrete deficit family
described below. A sufficient
substitute for the ratio-limit sequence is now proved from the geometric
shadow estimates, as detailed below. The visual carrier is
matched explicitly. Pathwise concentration now supplies the return errors
without an additional differentiation hypothesis, as detailed below.

The invariant visual carrier matching is now completed.
`InvariantRestrictionCocycle` proves that translation commutes with invariant
restriction and that restriction preserves the actual derivatives and log
cocycles. `InvariantVisualShadows` supplies uniform positive inverse-shadow
mass on every positive invariant carrier; `InvariantVisualShadowComparison`
absorbs its total mass into a uniform exponential constant.
`FuchsianVisualCarrier` combines this with the actual hitting law under
nonsingularity, obtaining equivalent measures, unchanged densities/cocycles,
and simultaneous visual shadow bounds. This does not establish equivalence
with unrestricted visual measure.

The return-cover construction is also checked with more primitive inputs.
`ShadowReturnConcentration` bounds pulled-back error by `exp(2C)` times total
mass times relative shadow error. `VanishingErrorReturnCover` turns vanishing
error mass and eventual coverage into actual returns. `ShrinkingExceptionalSets`
and `AdjustableExceptionalCover` construct finite eventual coverage by
compactness and orbit escape: the shadow parameter is chosen to make the
exceptional region small before taking the eventual limit in the sequence.
`ConcentratingShadowReturnCover` combines these steps, and
`FuchsianShadowReturnCover` supplies countability, quasi-invariance, and escape
from finite exceptional sets for the actual walk. Its uniform harmonic
cocycle estimate, relative-concentration limit, and adjustable exceptional-set
convergence remain explicit hypotheses. In particular, no false inference is
made that a fixed-size visual inverse shadow has complement shrinking to a
point. The harmonic/mixed-shadow data remain to be constructed. The newer
pathwise assembly avoids the separate differentiating-sequence requirement.

The visual exceptional-set convergence is now proved independently in
`VisualShadowFrames`, `FrameRealBoundaryContinuity`, and
`VisualShadowExceptionalLimit`. A normalized frame lies in a compact orbit-map
fiber; a convergent subsequence and joint boundary continuity put the inverse
complement into any prescribed neighborhood after choosing the cap parameter.
`FuchsianVisualShadowCover` derives finite corrected eventual coverage.
`MixedVisualExceptionalLimit` adds this proved visual geometry to a second
family's finite exceptional-set convergence. `MixedVisualShadowReturnCover`
combines the resulting cover with relative concentration to obtain returns.
No visual exceptional convergence remains assumed in these mixed statements.
These general-sequence statements retain explicit relative-concentration
hypotheses. For actual walk paths, the newer results below discharge that
measure-theoretic input under the necessary geometric controls. The second
family's exceptional convergence remains unproved. The concrete family
described below now supplies its local cocycle estimate.

Pathwise boundary-event concentration is now proved, not assumed.
`WalkPrefixFiltration` identifies the full product sigma-algebra as the
supremum of the finite-prefix filtration. `FiniteIndependentConditioning` and
`WalkPrefixConditioning` compute conditional expectations using the independent
tail; `WalkBoundaryTimeCocycle` iterates equivariance. `WalkBoundaryConcentration`
applies Levy convergence, and `FuchsianBoundaryConcentration` derives first-step
equivariance for the actual projective selector from geometric convergence.
For every measurable E, the translated hitting mass of E tends almost surely
to the indicator that the endpoint lies in E. The vanishing complement mass
also transfers to every finite reference measure dominated by the hitting law.

`TranslatedConcentrationReturnCover` bounds return error in any shadow by this
complement mass. `FuchsianPathReturnCover` therefore gives visual returns
unconditionally on almost every path ending in E; its mixed version needs
only the harmonic family's finite exceptional-set convergence. The return
step no longer requires relative differentiation, positive mixed mass, or
cocycle bounds along these paths. `TranslatedShadowConcentration` and
`FuchsianShadowPathConcentration` additionally derive relative concentration
from a uniform inverse-shadow mass lower bound and cocycle error estimate.
Thus relative concentration along actual paths is available once those
geometric controls are established. The comparison sequence is now obtained
from that concentration by the following checked argument. The uniform
Green upper bound remains unproved. Local harmonic cocycle control for the
new deficit sets follows from their definition, but their uniform mass and
exceptional-set geometry still need proof.

The mass-ratio limit is no longer an independent analytic obligation.
`BoundedDensityWindows` produces a positive measurable bounded-log-density
window and restricted measure comparison. `ConcentratedShadowComparison`
uses simultaneous relative concentration to bound the log shadow-mass ratio
by the window bound plus log 2, eventually. Exponential estimates bound the
magnitude discrepancy, and a finite-prefix argument makes the bound global
along the sequence. `InverseShadowMassFromBounds` obtains the inverse-mass
lower bound needed for concentration from the lower exponential estimate and
local cocycle control. `FuchsianShadowPathComparison` therefore gives bounded
magnitude discrepancy along actual paths ending in the window, without a
mass-ratio limit or separate differentiation assumption.

`FuchsianShadowGeometryRigidity` assembles this into global rigidity. It
constructs the window, selects a path in its positive-probability endpoint
event, and uses eventual geometric coverage to construct the return cover.
The countable shadow-family parameter may be chosen after the path, because
pathwise comparison holds simultaneously for every parameter. The conclusion
is a global bound on the difference of the two magnitudes. Its remaining
inputs are the equivalent finite quasi-invariant reference measure, common
exponential shadow estimates, local cocycle estimates, finite correction
bounds, and eventual corrected coverage along a subsequence of almost every
path. The matched visual carrier supplies the reference-side machinery; the
uniform harmonic/mixed shadow mass and exceptional-set coverage are now
derived from the single compactness premise described below.
The unrestricted singularity theorem remains unfinished. The old ratio-limit
rigidity theorem is now a corollary of `BoundedSequenceShadowRigidity`.

A concrete shadow family is now defined in `CocycleDeficitShadows` and
`FuchsianGreenDeficitShadows`: the target point eta lies in the shadow when
`d_G(1,g) - sigma_nu(g,g^-1 eta) <= R`. Measurability, monotonicity, fixed-element
exhaustion, the local cocycle estimate, and exponential mass bounds retaining
inverse mass are proved. The element-dependent threshold
`d_G(1,g)+d_G(g,1)` makes the inverse shadow conull, but does not supply a
threshold uniform in g. `FuchsianMixedDeficitShadows` constructs the canonical
countable mixed family with harmonic allowance N and visual cap 1/(N+1),
and proves cofinality in both parameters.

`ShadowEstimatesFromInverseMass` absorbs a positive inverse-mass lower bound
into an additive exponential constant. `FuchsianMixedDeficitEstimates` gives
both hitting and invariant-visual-carrier mass/cocycle estimates for the same
concrete mixed sets. Uniform positive inverse mass is still an input. The
local cocycle bounds themselves no longer require an unspecified harmonic
shadow theorem. This moves the missing content into uniform mass control
and exceptional-set convergence; it does not prove either automatically.

The required exceptional containment is formulated modulo hitting-null sets.
A raw Radon–Nikodym representative need not have pointwise regularity on its
null domain. `AEExceptionalShadowCover` proves that countability and
quasi-invariance suffice to transfer such almost-everywhere containment through
finite corrections. `FuchsianDeficitAECover` combines this harmonic input with
the proved visual convergence and countable cofinality. The coverage input of
`FuchsianShadowGeometryRigidity` has been weakened accordingly to an
almost-everywhere boundary cover. The stronger pointwise cover is retained
only as a sufficient special case.

`FuchsianDeficitCompactness` now names the precise remaining geometric
premise: every group sequence has a strict subsequence with finite exceptional
set Z, and for every open U containing Z, some fixed real allowance R makes
the inverse deficit-shadow complement lie in U almost everywhere at all
sufficiently late times. It is now proved for a proper ideal limit set or the existence of a
parabolic. The current remaining route is the first-kind structural
implication stated above; no unrestricted compactness axiom is introduced.
The hitting measure's atomlessness is proved independently from stationarity
and infinite boundary orbits.

`ExceptionalShadowUniformMass` derives uniform almost-full inverse mass
from this compactness premise by contradiction: a sequence of uniformly
positive complements, finite-set nullity, and outer regularity conflict with
subsequential exceptional containment. `FuchsianMixedDeficitUniformMass`
transfers the estimate to every finite measure absolutely continuous with
respect to both the hitting and visual laws, and combines it with the visual
estimate for the canonical mixed family. Positive subprobability references
then admit a common lower inverse-mass bound at all sufficiently large
indices.

`FuchsianSingularityFromDeficitCompactness` completes the conditional
assembly: under nonsingularity it constructs the invariant visual carrier,
chooses a common index threshold, supplies all exponential/cocycle estimates
and finite corrections, and uses compactness to obtain the corrected cover.
The checked rigidity and Green-to-quasiconvexity reductions give singularity.
There is no separate uniform-mass, density-bound, or final-assembly premise.
The unresolved task is proving `FuchsianDeficitCompactness` in the remaining
cases (or replacing it with a proved sufficient result). The unrestricted
theorem remains unfinished.

Two additional components of a possible construction of the missing
compactness property are now checked:

- `BoundaryFactorCocycleBounds` proves local deficit bounds descend through
  an equivariant measured factor by localized domination of translated
  measures. `BoundaryFactorDeficitCompactness` adds continuity to transfer
  the full subsequential finite-exception property. The exceptional set
  becomes its image; no finite-fiber assumption is needed.
  `FuchsianDeficitCompactnessOfFactor` connects this transfer to the actual
  hitting measure. No auxiliary boundary or factor is asserted to exist.
- `FiniteEntranceHarmonicDeficit` derives a uniform bound
  `H(x) <= C_A G(x,1)` from a finite entrance upper representation of a
  normalized positive superharmonic function. Its stationary-density
  specialization yields the required local cocycle deficit bound without
  an L² hypothesis on the harmonic functions.
  `FuchsianDeficitFiniteEntrance` assembles this into compactness when the
  corresponding finite entrance representations are supplied away from the
  exceptional neighborhoods. The representations now follow from the
  pathwise visit condition as described next; a suitable family of geometric
  entrance sets remains to be constructed.

Thus the new modules prove the quotient transfer and the analytic consequence
of an entrance representation, not the missing source-boundary geometry.
The existing cocompact Ancona estimates cannot be invoked unchanged to fill
that gap: their formal statements include cocompact geometric hypotheses.

`BoundaryFirstEntrance` proves the joint first-entrance/boundary probability
identity by deterministic-time independence. `BoundaryFiniteEntranceRepresentation`
derives an exact finite mixture of restricted translated boundary laws when
the boundary event forces a visit to the finite set. `FiniteTranslateDensity`
then proves equality of the corresponding real Radon–Nikodym densities on
the region, and `FuchsianFiniteEntrancePaths` supplies this identity for the
actual hitting law. No stopping formula or density representation remains
assumed once the pathwise visit condition is given.

`FuchsianFiniteSeparatorRegions` derives that condition from deterministic
trapping regions: permitted exits require visiting a finite set, and the
region's orbit closure has ideal boundary inside the exceptional neighborhood.
It also proves convergence from every starting vertex to that vertex acting
on the named boundary map. The family of regions is still an explicit
geometric input. This is a sufficient finite-separator route, not a claim
that all groups satisfying deficit compactness must have finite separators.

`CuspStripFiniteness` proves a concrete local finiteness result. The bounds
`Im(g z) <= C` and `Im(J g z) <= D`, where `J=boundaryPoleMatrix 0`, give
`Im(g z) >= 1/(D*(R^2+1))` inside the axis-ratio strip of radius R.
The strip lies in a compact rectangle, and its group vertices are finite.
Two nontrivial parabolic shears at the endpoints zero and infinity supply
these height bounds by discreteness and conjugation, so the finite-jump
strip separator is finite with those explicit group-membership assumptions.
Normalization is now proved by `ParabolicFixedPointCharts`: a prescribed
chart at a parabolic fixed point conjugates that element to a nonzero shear.
`ProjectiveCuspStrips` therefore proves strip finiteness at arbitrary pairs
of distinct parabolic fixed points, using the full SL₂ lift and projection.
`FiniteExitEnlargement` and `ProjectiveCuspExitSets` construct a finite set
containing every possible starting vertex of a supported exit from the
negative half-plane. `ChartBoundaryArcs` verifies its closed ideal arc and
eventual negative-side membership for convergence to its interior.

`FuchsianCuspDeficit` now derives the actual pathwise visit condition, exact
hitting-density entrance representation, and uniform local Green-deficit
bound directly from these two cusps. These are constructed local regions,
not an assumed stopping representation. Still missing is selection of
enough endpoint pairs to handle arbitrary sequences, including the relevant
limit-set gaps, and coverage of the remaining Fuchsian geometries. No
unrestricted compactness or singularity conclusion is asserted.

The needed relative density of cusp endpoints is now proved. `EndpointImageBounds`
and `BoundaryOrbitMinimality` show that the closure of every boundary orbit
of a nonelementary projective group contains its ideal orbit limit set.
`ParabolicFixedPointDensity` applies this to conjugate parabolic fixed points;
`ParabolicIdealLimits` proves convergence of parabolic powers and the reverse
containment. Their closure is therefore exactly the limit set whenever a
parabolic exists. This does not identify that set with the whole circle or
construct the required shrinking regions across complementary gaps.

The full-limit-set cusp case is now completed independently of a boundary
factor. `IntervalBoundaryCharts` explicitly normalizes bounded intervals with
the correct orientation. `ShrinkingBoundaryCharts` uses dense parabolic
endpoints to construct arbitrarily small closed cusp arcs containing any
chosen ideal point in their interior. `ProjectiveOrbitSubsequences` obtains
a finite-valued tail or an ideal limit after subsequence extraction. The
first case has entrance at time zero; the second uses the constructed cusp
exit sets. `FuchsianFullLimitCuspSingularity` consequently proves deficit
compactness and actual hitting-measure singularity under the explicit full
ideal limit set and parabolic hypotheses, with no symmetry assumption.

This full-limit-set specialization is now superseded by the general
parabolic/proper-limit-set theorem described at the start of this file.
A statement directly in terms of covolume would still require the relevant
structural connection; the full target is reduced to the stated first-kind,
parabolic-free compactness implication.

For mathematical context, Blachère–Haïssinsky–Mathieu,
[§5.5, Proposition 5.5 and Theorem 1.10](https://www.numdam.org/item/10.24033/asens.2153.pdf),
distinguish the abstract group boundary from the geometric limit boundary
in the cusp case. Their printed statements there assume symmetry. This is
background for the investigation, not a theorem imported as a Lean axiom
or a justification for omitting hypotheses in this nonsymmetric project.

The preliminary dynamics and actual hitting law no longer need compactness:

- `NonelementaryHyperbolic.lean` proves existence of a hyperbolic element from
  infinite geometric orbits, using the checked elliptic/parabolic commutator
  identities and their common-fixed-point consequences.
- `ProjectiveNonelementaryDynamics.lean` proves a free subgroup and the spectral
  gap for the original projective walk, with no cocompactness assumption.
- `FuchsianHittingMeasure.lean` supplies actual geometric convergence,
  stationarity, quasi-invariance, and uniqueness of the limit law for every
  discrete nonelementary projective group under the finite-law assumptions.
- `FuchsianLimitSet.lean` proves concentration on the actual ideal orbit limit
  set and singularity when that set is visual-null. The visual-null hypothesis
  is now discharged for noncocompact quasiconvex orbits by the modules above.
  No unrestricted infinite-covolume nullity theorem is claimed.

The quantitative Green/word comparison used in the rigidity reduction is now
proved independently of geometry. `GreenWordComparison.lean` gives linear
bounds for the logarithmic normalized Green function in the symmetric word
distance; the original projective spectral gap is supplied internally.
`ProjectiveParabolic.lean` classifies squared-trace-four nonidentity elements
as projective conjugates of nontrivial upper shears and proves their sublinear
hyperbolic displacement. The obstruction theorem then excludes bounded
Green/hyperbolic comparison. `FreeGroupPowerLength.lean`,
`SchreierRetraction.lean`, `FiniteIndexFreeLength.lean`, and `PowerWordGrowth.lean`
now prove the necessary word-growth estimate for every infinite-order element
of a group with a free subgroup of finite index. `ParabolicInfiniteOrder.lean`
proves that projective parabolics have infinite order, so
`VirtuallyFreeParabolic.lean` needs no separate word-growth assumption.

`StableGreenLength.lean` proves existence of the normalized power limit via
Fekete's lemma. `StableParabolicObstruction.lean` strengthens the contradiction:
the normalized Green/hyperbolic discrepancy along a parabolic has a strictly
positive limit for every real scaling factor, excluding even sublinear error.
The finite-index free-subgroup hypothesis is explicit in these results.

The older power-growth obstruction retains its explicit finite-index
free-subgroup hypothesis. The new `discrete_parabolic_no_green_upper` and
`discrete_parabolic_no_green_comparison` theorems remove that hypothesis by
passing through the proved orbit quasiconvexity implication. For the current
Green-distance route, the analytic nonsingularity-to-upper-bound implication
is still unproved. None of these statements is assumed as an axiom. The
structural/relative-hyperbolicity prerequisites of the cited external rigidity
theorem remain unfinished; the comparison-to-quasiconvexity implication and
visual-null-or-full alternative after quasiconvexity are now proved.

The cocompact geometric Martin/Naïm construction must not be silently applied
without compactness of the hyperbolic orbit quotient. The unrestricted
singularity theorem remains unfinished; the quasiconvex case is complete.

## 3. Matching the original projective formulation — completed

`FuchsianCocompactSingularity.lean` proves the cocompact result for the actual
hitting law of a subgroup of `PSL(2, ℝ)`. The proof constructs the full
`SL(2, ℝ)` inverse image, verifies discreteness and cocompactness, lifts every
jump with both signs at half weight, and proves semigroup generation. The
projection preserves the original iid path law and every geometric trajectory.
The resulting boundary probability is proved to be the original hitting law.

Nonelementarity is the classical absence of a finite orbit in the hyperbolic
plane together with its ideal boundary, formalized as `ProjectiveNonelementary`.
The derived infinite-boundary-orbit hypothesis is not an additional assumption
of the final theorem. No equivalence with a separate limit-set-cardinality
convention is needed or asserted here.

The main target retains semigroup generation. A general weakening to group
generation has not been asserted. No symmetry assumption occurs in the final
cocompact theorem.

## 4. Earlier branches that are not required by the completed route

Some older modules investigate contraction inside killed geometric domains.
Their uniform relative-comparison hypotheses remain unproved. The completed
Martin/Naïm route uses ordinary Ancona, global harmonic minimality, and strong
strip limits instead; it does not invoke those unproved relative comparisons.

The chronological dependency map is retained in `DEPENDENCY_HISTORY.md`.
Its older statements that the kernel, current, or Fourier assembly are missing
have been superseded by the checked modules listed in `README.md`.

## Verification boundary

`verify.py` builds all modules and audits every theorem/definition transitively.
Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms are
allowed. This verifies the stated hypotheses and conclusions; it does not
supply the missing noncocompact theorem and the external reduction described
above.
