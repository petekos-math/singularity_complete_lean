> Historical snapshot before the final Dirichlet-end argument. See README.md for the current theorem.

# Lean formalization of hitting-measure singularity

**Singularity is proved in Lean for discrete nonelementary PSL₂ groups with
quasiconvex orbits (including the cocompact case), for every group containing
a parabolic, and for every proper ideal limit set, without symmetry.
The unrestricted case remains unfinished.** The current source contains
2564 checked theorem/definition declarations in 512 modules. No additional axioms
or admitted proofs are permitted by the audit.

## Remaining obligation

The unchecked case now has **full ideal limit set and no parabolics**.
The remaining geometric theorem is that a finitely generated discrete
nonelementary group with these properties is cocompact. Finite generation
comes from the finite semigroup-generating support. This structural theorem
has not been formalized or assumed as an axiom.

[FuchsianFirstKindReduction.lean](Singularity/FuchsianFirstKindReduction.lean)
proves that any nonsingular example would have full limit set, no parabolic,
and noncompact quotient. Its final assembly proves singularity conditional
only on the missing structural implication. No missing shadow, entrance,
or cusp-density estimate is left in the parabolic/proper-limit-set cases.

## Main results

`parabolic_or_proper_limitSet_fuchsian_hittingMeasure_singular` in
[FuchsianCuspOrProperLimitSingularity.lean](Singularity/FuchsianCuspOrProperLimitSingularity.lean)
proves singularity for the actual finite positive semigroup-generating walk
if **either** the ideal limit set is proper **or** Γ contains a parabolic.
The separate corollaries are `parabolic_fuchsian_hittingMeasure_singular`
and `proper_limitSet_fuchsian_hittingMeasure_singular`; the combined
Lebesgue-chart corollary is also proved. No full-limit-set, visual-nullity,
quasiconvexity, or symmetry hypothesis is needed for the parabolic result.

The geometric step uses parabolic fixed points together with points outside
the limit set. `ProjectiveEndpointHeight` bounds orbit height at both kinds
of endpoints; `ProjectiveEndpointStrips` constructs finite strips and exit
sets. `DenseStripEndpoints` proves density of the available endpoints,
including across complementary gaps. Shrinking charts and subsequence
extraction then prove the entire deficit-compactness premise.


`full_limitSet_parabolic_fuchsian_hittingMeasure_singular` in
[FuchsianFullLimitCuspSingularity.lean](Singularity/FuchsianFullLimitCuspSingularity.lean)
proves singularity under the usual discrete nonelementary, finite positive
semigroup-generating walk assumptions and these two geometric hypotheses:

- `projectiveOrbitLimitSet Γ z = Set.univ`;
- Γ contains an element satisfying `ProjectiveParabolic`.

Its real-chart Lebesgue corollary is proved as well. Deficit compactness,
finite path separation, and entrance representations are all proved from
these hypotheses; they are no longer additional premises in this case.
This earlier full-limit-set specialization is subsumed by the newer
parabolic theorem above. A theorem stated directly from a standard
nonuniform-lattice/covolume hypothesis would still need its structural
connection to the proved geometric cases.

`quasiconvex_fuchsian_hittingMeasure_singular` in
[FuchsianQuasiconvexSingularity.lean](Singularity/FuchsianQuasiconvexSingularity.lean)
proves singularity of the actual hitting measure against visual measure for a
discrete nonelementary subgroup of `PSL(2, ℝ)` with a quasiconvex orbit and a
finite positive semigroup-generating probability law. It includes noncocompact
quasiconvex groups. The Lebesgue-chart corollary is also checked. The orbit
quasiconvexity hypothesis is explicit: all metric segments between orbit points
must lie within a fixed distance of the orbit. No limit-set measure assumption
remains in this theorem.

`cocompact_fuchsian_hittingMeasure_singular` in
[FuchsianCocompactSingularity.lean](Singularity/FuchsianCocompactSingularity.lean)
proves mutual singularity of the actual hitting measure and visual measure,
under these explicit hypotheses:

- `Γ` is a discrete subgroup of `PSL(2, ℝ)`;
- its orbit quotient of the hyperbolic upper half-plane is compact;
- `Γ` is nonelementary: it has no finite orbit in the hyperbolic plane together
  with its ideal boundary;
- `s : Finset Γ` carries strictly positive weights `μ`, totaling one;
- `s` generates `Γ` as a semigroup.

There is no symmetry, spectral-gap, matrix-lift, or separate boundary-orbit
hypothesis. `cocompact_fuchsian_hittingMeasure_singular_lebesgue` gives the
corresponding Lebesgue singularity in the real boundary chart.
`cocompact_fuchsian_boundaryMap_tendsto` proves almost-sure convergence of the
original projective random walk to the named boundary map, and
`cocompact_fuchsian_hittingLaw_singular` gives singularity for any other
almost-sure version of that limit.

`ProjectiveNonelementary` uses the classical finite-geometric-orbit convention,
as in [Jacques–Short, §1 and §10](https://arxiv.org/abs/1609.00576). Its disjoint
sum represents the set of interior and ideal points and their group action;
it does not equip the compactification with the sum topology. Equivalence with
other definitions involving cardinality of the limit set is not used or claimed.

The earlier `SL(2, ℝ)` theorem remains in
[CocompactHittingSingularity.lean](Singularity/CocompactHittingSingularity.lean).
It also proves singularity of both forward and reflected hitting laws.
The spectral gap, coordinate normalization, Naïm current, finite invariant
quotient probability, stable-product transfer, and Fourier operators are all
supplied by proofs. See [DEPENDENCIES.md](DEPENDENCIES.md) for the remaining
noncocompact work.

## General nonelementary hitting measures — no compactness assumption

[FuchsianHittingMeasure.lean](Singularity/FuchsianHittingMeasure.lean) now proves
almost-sure convergence to the named projective boundary map, stationarity,
equivalence with every group translate, and independence of the choice of
almost-sure limit version for every discrete nonelementary projective group
and finite positive semigroup-generating probability support.

This uses a newly checked algebraic argument. If all traces have absolute
value at most two, the elliptic and parabolic commutator identities force a
common interior or boundary fixed point. Nonelementarity therefore supplies
a hyperbolic element without cocompactness. Its north–south dynamics descends
to the original projective group and produces a free subgroup.
`projectiveNonelementary_rightMarkov_gap` proves the spectral gap of the
original right Markov operator, without symmetry or laziness.

[FuchsianLimitSet.lean](Singularity/FuchsianLimitSet.lean) defines the ideal
orbit limit set through closure in the compact sphere and proves that it
carries the actual hitting probability. The theorem
`fuchsian_hittingMeasure_singular_of_null_limitSet` gives singularity under the
explicit hypothesis that this set has zero visual measure. The new quasiconvex
argument derives this nullity for noncocompact quasiconvex orbits. Nullity is not
asserted for all noncocompact groups.

## Geometric reduction beyond cocompactness

[QuasiconvexParabolic.lean](Singularity/QuasiconvexParabolic.lean) proves that a
discrete projective group containing a parabolic has no quasiconvex orbit.
This theorem needs neither finite generation nor a finite-index free subgroup.
The proof first bounds orbit heights in coordinates where the parabolic is a
horizontal translation. Explicit geodesic midpoints between opposite powers
rise beyond every fixed neighborhood of the orbit. Conjugation and the sign
lift remove the choice of coordinates.

[QuasiconvexFullBoundary.lean](Singularity/QuasiconvexFullBoundary.lean) proves
that a quasiconvex set accumulating on the entire ideal boundary is uniformly
dense: a quasiconvexity constant `D` gives a covering radius `D + 2 * log 4`.
For a projective orbit it constructs a compact quotient from this cover.
The full-limit-set hypothesis is explicit.

[QuasiconvexLimitSetDichotomy.lean](Singularity/QuasiconvexLimitSetDichotomy.lean)
now proves that a quasiconvex orbit's limit set is visual-null or the entire
boundary. Its proof uses:

- Invariance of the actual limit set and constancy of its visual mass along
  the orbit (`LimitSetDynamics`, `VisualPoissonOrbit`).
- A cosine-ratio estimate for triangle excess and orbit tracking of vertical
  approaches to every finite limit point (`VerticalRayExcess`, `QuasiconvexConical`).
- Lebesgue density, exact affine rescaling, and a finite-measure tail argument
  proving vertical Poisson concentration (`DensityRescaling`,
  `BoundedDensityConcentration`, `PoissonDensityPoint`).

Positive visual mass supplies a density point. Concentration there and bounded
distance to the orbit force full visual mass; closedness and full support then
force full boundary. This dichotomy requires neither discreteness nor finite
generation, only the quasiconvex orbit hypothesis.

[FuchsianQuasiconvexSingularity.lean](Singularity/FuchsianQuasiconvexSingularity.lean)
combines the dichotomy with the existing singularity results. Its final theorem,
`fuchsian_singularity_of_quasiconvex_rigidity`, leaves just one explicit premise:
nonsingularity of the actual hitting measure implies a quasiconvex orbit.
That substantial rigidity statement is still unproved. Earlier conditional
reductions remain in `FuchsianQuasiconvexReduction.lean` for reference, but the
limit-set premise is now discharged whenever the orbit is quasiconvex.

## General hitting cocycles and the remaining analytic step

[FuchsianHittingErgodicity.lean](Singularity/FuchsianHittingErgodicity.lean)
proves the zero–one law and the singular-or-absolutely-continuous dichotomy for
the actual projective hitting law, without cocompactness. Under nonsingularity,
[FuchsianDensityCocycle.lean](Singularity/FuchsianDensityCocycle.lean) constructs
an invariant hitting-conull set `E` on which the hitting law and the restricted
visual measure have the same null sets. It does not assert equivalence with
the unrestricted visual measure.

[StationaryLogCocycle.lean](Singularity/StationaryLogCocycle.lean) defines
`sigma(g,xi) = -log(d(g⁻¹_*nu)/dnu(xi))` using actual Radon–Nikodym derivatives.
It proves the exact additive cocycle identity and

```text
-greenDistance(g,1) ≤ sigma(g,xi) ≤ greenDistance(1,g).
```

`InvariantConullSet` and `StationaryCocycleDomain` put all these identities on
one measurable invariant conull domain. `FuchsianLogCocycle` supplies the
spectral gap internally and bounds the cocycle linearly in word length.

[RadonNikodymCoboundary.lean](Singularity/RadonNikodymCoboundary.lean) proves
that changing from visual measure `m` to an absolutely continuous hitting law
`nu = h m` changes the logarithmic cocycle by exactly
`log h(xi) - log h(g xi)`. `VisualLogCocycle` bounds the visual term by hyperbolic
displacement. Consequently the hitting cocycle is bounded by displacement
plus the two explicit absolute log-density terms.

No uniform density bound is inferred from absolute continuity. The density
upgrade and the shadow estimates connecting cocycle magnitudes back to Green
distance in the unrestricted setting remain unproved. These are part of the
remaining nonsingularity-to-Green-comparison rigidity step, not consequences
claimed by the new cocycle modules.

## Visual shadows and transfer to the hitting law

[VisualShadows.lean](Singularity/VisualShadows.lean) constructs explicit open
boundary caps by transporting the cap `|xi| > exp(t) * r`, together with the
point at infinity, along a chosen oriented hyperbolic axis. For `r > 0`, put
`C(r) = (r² + 1) / r²` and let `a(r)` be the visual mass of the normalized cap.
The checked bounds are

```text
exp(-dist(z,w)) * a(r) ≤ m_z(shadow(z,w,r))
  ≤ C(r) * exp(-dist(z,w)) * a(r).
```

`VisualShadowDensity` proves the upper comparison on every measurable subset
of the cap. `VisualShadowCocycle` consequently proves that the visual cocycle
on the inverse shadow of `g z` differs from `dist(z,g z)` by at most `log C(r)`.
`VisualShadowSize` bounds every inverse-shadow complement by `2r/pi` and
proves that fixed-parameter shadows have vanishing mass as their centers escape.
These caps depend on a chosen axis; no equivariance of that choice or
identification with a random-walk shadow is asserted.

[FiniteMeasureAbsoluteContinuity.lean](Singularity/FiniteMeasureAbsoluteContinuity.lean)
and `AbsolutelyContinuousVisualShadows` transfer uniform inverse-shadow
fullness and vanishing shadow mass to any absolutely continuous finite measure.
[FuchsianVisualShadows.lean](Singularity/FuchsianVisualShadows.lean) applies
these facts to the actual hitting law under nonsingularity. It also proves,
simultaneously for all group elements, the inverse-shadow bound

```text
|sigma_nu(g,xi) - dist(z,g z) - log h(xi) + log h(g xi)| ≤ log C(r).
```

The density coboundary remains explicit. These results do not bound it
uniformly or establish the missing upper Green-distance comparison.

## Measure-theoretic shadow rigidity — checked with geometric inputs explicit

[CocycleShadowMeasure.lean](Singularity/CocycleShadowMeasure.lean) proves the
exact formula `nu(g E) = integral_E exp(-sigma_nu(g,xi)) dnu`. A local cocycle
bound therefore gives two-sided exponential image-mass estimates.
`MixedShadowMeasure` applies this to intersections: when both inverse-shadow
complements have mass at most one quarter, their intersection retains at
least half the inverse mass and has the corresponding exponential bounds.

`StationaryGreenMeasure` integrates the already proved directed Green
cocycle bounds. [FuchsianGreenShadows.lean](Singularity/FuchsianGreenShadows.lean)
then proves, under nonsingularity, that sufficiently wide visual shadows have
hitting mass at least `(1-epsilon) * exp(-greenDistance(1,g))`, uniformly in
`g`. This is a lower mass bound. The upper mass bound of this order remains
unproved. That module also checks that an upper shadow bound and domination
`m <= exp(K) nu` imply the required upper Green-distance comparison.

[ShadowRigidityFromReturnCover.lean](Singularity/ShadowRigidityFromReturnCover.lean)
combines the following checked measure-theoretic steps:

- `ShadowRatioRigidity`: a positive finite limit of common-shadow mass ratios
  bounds the magnitude difference along that sequence.
- `ReturnCoverDensityRigidity`: a finite corrected return cover into a bounded
  density window upgrades that sequence bound to an essentially bounded log
  density on the carrier.
- `LogDensityMeasureComparison`: equivalent measures with bounded log density
  are uniformly comparable. Equivalence is required explicitly here.
- `ShadowMagnitudeComparison`: comparable measures with common exponential
  shadow estimates have uniformly comparable magnitudes.

`FuchsianShadowCorrections` supplies the finite correction bounds for the
actual hitting and visual cocycles under nonsingularity, without assuming a
bounded density.

This proves the measure-theoretic calculation used in the mixed-shadow route
of [Kim–Zimmer, Sections 6–7](https://arxiv.org/html/2505.16556v3), with its inputs
exposed. It does not verify their full PS-system theorem for the present walk.
The required harmonic/Green shadow geometry remains to be proved for the
concrete deficit-shadow family now constructed below. The
visual carrier, pathwise concentration, bounded shadow-mass comparison, and
return-cover construction are checked as described below.
The unrestricted singularity theorem is still unfinished.

## Invariant visual carrier and return-cover construction

[FuchsianVisualCarrier.lean](Singularity/FuchsianVisualCarrier.lean) now
supplies a positive-mass invariant carrier under nonsingularity, with the
restricted visual measure equivalent to the actual hitting law. The density
relative to the restricted reference agrees with the original density, and
the restricted visual cocycle agrees with the original visual cocycle.
`InvariantRestrictionCocycle` proves these restriction identities generically.
`InvariantVisualShadows` and `InvariantVisualShadowComparison` prove uniform
exponential visual shadow estimates on the carrier, absorbing its possibly
smaller total mass into the additive constant. Full visual measure equivalence
is not assumed or deduced.

[ShadowReturnConcentration.lean](Singularity/ShadowReturnConcentration.lean)
proves the quantitative error transfer

```text
nu(g^-1(S \ E)) <= exp(2C) * nu(univ) * nu(S \ E) / nu(S)
```

for the real masses of a positive-mass shadow with cocycle error at most `C`.
Relative concentration in shadows therefore gives vanishing inverse error.
`VanishingErrorReturnCover` converts vanishing errors and eventual shadow
coverage into actual returns, using quasi-invariance for the corrections.

`ShrinkingExceptionalSets` gives the topological coverage lemma.
[AdjustableExceptionalCover.lean](Singularity/AdjustableExceptionalCover.lean)
keeps the essential parameter choice explicit: enlarging shadows makes the
exceptional regions small, after which one fixed parameter and finitely many
corrections give eventual coverage. It does not require complements for one
fixed shadow size to shrink to points.

`ConcentratingShadowReturnCover` assembles this construction.
[FuchsianShadowReturnCover.lean](Singularity/FuchsianShadowReturnCover.lean)
supplies countability, quasi-invariance, and escape from finite exceptional
sets for the actual nonelementary walk. The harmonic cocycle estimates,
relative concentration, and adjustable exceptional-set convergence are still
explicit hypotheses of that general-sequence theorem. The pathwise results
below now supply concentration for actual walk sequences; constructing the
harmonic shadow geometry remains unfinished.

## Visual exceptional-point convergence — completed

[VisualShadowFrames.lean](Singularity/VisualShadowFrames.lean) identifies each
inverse visual-shadow complement with the image of `[-r,r]` under a normalized
matrix sending `i` to the fixed basepoint. Properness makes these matrices lie
in a compact set. `FrameRealBoundaryContinuity` proves the joint continuity
needed to control their action on a small real interval.

[VisualShadowExceptionalLimit.lean](Singularity/VisualShadowExceptionalLimit.lean)
extracts a subsequence and one exceptional boundary point. For every open
neighborhood of that point, some positive parameter makes all sufficiently
late inverse complements lie in the neighborhood. This is an adjustable-size
statement; a fixed-size complement need not shrink to a point.

`FuchsianVisualShadowCover` derives finite corrected eventual coverage for
any sequence in a nonelementary projective group, without discreteness or
cocompactness. `MixedVisualExceptionalLimit` combines this with a second
shadow family, adding at most one exceptional point to that family's finite
exceptional set. `MixedVisualShadowReturnCover` then produces corrected
returns from relative concentration in the mixed shadows and a cocycle bound
on the second family. The visual convergence and coverage are now supplied
internally. The second family's exceptional-set data, cocycle estimates,
and mixed-shadow positivity and concentration remain explicit hypotheses.

## Boundary concentration along actual paths — completed

[FuchsianBoundaryConcentration.lean](Singularity/FuchsianBoundaryConcentration.lean)
proves for each measurable boundary event `E` that, almost surely,

```text
nu(w_n^-1 E) -> 1_E(boundary limit).
```

`WalkPrefixFiltration` proves that the finite-prefix sigma-algebras exhaust
the actual product path space. `FiniteIndependentConditioning` and
`WalkPrefixConditioning` identify conditional expectations by averaging the
independent future. `WalkBoundaryTimeCocycle` iterates boundary equivariance,
and `WalkBoundaryConcentration` applies Levy's upward convergence theorem.
The original projective selector's equivariance follows from geometric
convergence, so no compactness or auxiliary boundary identification is assumed.
Concentration transfers to every finite measure absolutely continuous with
respect to the hitting law, including the matched visual carrier.

[FuchsianPathReturnCover.lean](Singularity/FuchsianPathReturnCover.lean) uses
this concentration to obtain finite corrected visual-shadow returns along
almost every path ending in `E`. For mixed shadows, only the second family's
finite exceptional-set convergence remains an input to this return step.
No shadow cocycle estimate, positive shadow mass, or relative-error limit is
required for these pathwise return covers.

`TranslatedShadowConcentration` also proves the converse error transfer:
relative shadow error is at most `exp(2C)/c` times the pulled-back complement
mass when inverse-shadow mass is at least `c > 0` and cocycle error at most
`C`. `FuchsianShadowPathConcentration` thus supplies relative concentration
along actual paths under these geometric controls. For the concrete deficit
family below, the cocycle estimates are proved; uniform mass remains an input.
The next construction obtains sufficient shadow-mass comparison from these
geometric inputs, so a separate positive ratio-limit theorem is unnecessary.

## Path comparison and global rigidity from shadow geometry

[BoundedDensityWindows.lean](Singularity/BoundedDensityWindows.lean) constructs
a measurable positive-mass window with bounded log density and proves
exponential comparison of the restricted measures. In
`ConcentratedShadowComparison`, relative errors at most one half for both
measures imply shadow-mass comparison by a factor `2 * exp(M)`. Exponential
shadow estimates then bound the magnitude difference eventually; the finite
initial segment is absorbed into a single bound.

`InverseShadowMassFromBounds` obtains inverse mass at least `exp(-2C)` from
the lower exponential shadow estimate and local cocycle control. Thus no
separate inverse-mass lower bound is needed here.
[FuchsianShadowPathComparison.lean](Singularity/FuchsianShadowPathComparison.lean)
combines these estimates with actual path concentration to obtain bounded
magnitude discrepancy along almost every path ending in the density window.
No shadow-mass ratio limit is assumed.

[FuchsianShadowGeometryRigidity.lean](Singularity/FuchsianShadowGeometryRigidity.lean)
now constructs the window and chooses a suitable path internally. A countable
shadow family allows the parameter to be chosen after the path. Eventual
geometric coverage yields corrected returns, and
`BoundedSequenceShadowRigidity` upgrades the resulting bound to global
magnitude comparison. The older ratio-limit theorem is retained as a
corollary of this bounded-sequence core.

The remaining inputs of this assembled theorem are equivalence with a finite
quasi-invariant reference measure, common exponential shadow estimates and
local cocycle bounds, finite correction bounds, and eventual geometric
coverage along a subsequence of almost every path. The reference carrier and
visual estimates have been constructed. The concrete family below also
supplies the local harmonic estimate. The new compactness reduction below
derives uniform inverse mass and completes the conditional assembly.
Its geometric compactness premise remains unproved, so unrestricted
singularity is still unfinished.

## Concrete countable Green/visual shadows

[CocycleDeficitShadows.lean](Singularity/CocycleDeficitShadows.lean) defines the
shadow by the condition

```text
d_G(1,g) - sigma_nu(g, g^-1 eta) <= R.
```

`FuchsianGreenDeficitShadows` uses the actual hitting law and original Green
distance. Its local cocycle error is at most `R`, by the proved global Green
upper bound and the definition. The shadow is measurable and increases with
`R`; integer parameters exhaust it for each fixed `g`. The resulting mass
estimates retain the inverse-shadow mass explicitly. Neither pointwise
exhaustion nor the element-dependent conull threshold gives uniform mass
control over the group.

[FuchsianMixedDeficitShadows.lean](Singularity/FuchsianMixedDeficitShadows.lean)
intersects the deficit shadow at allowance `N` with the visual shadow at cap
`1/(N+1)`. This measurable increasing countable family is cofinal in both
parameters. Its harmonic cocycle estimate is proved simultaneously for all
indices and group elements. `FuchsianMixedDeficitEstimates` supplies the full
exponential and local cocycle estimates for the hitting law and an invariant
visual carrier, assuming uniform positive inverse-shadow mass for each side.
The additive constants absorb those lower bounds through `-log c`.

`AEExceptionalShadowCover` proves corrected eventual coverage from
exceptional-set containment modulo null sets. This distinction is necessary
for an actual Radon–Nikodym representative. In
[FuchsianDeficitAECover.lean](Singularity/FuchsianDeficitAECover.lean), visual
convergence and countable parameter cofinality are supplied internally; the
harmonic exceptional-set statement remains explicit. The global rigidity
theorem now accepts this almost-everywhere cover.

## Compactness: proved with a parabolic or proper ideal limit set

[FuchsianSingularityFromDeficitCompactness.lean](Singularity/FuchsianSingularityFromDeficitCompactness.lean)
proves `fuchsian_hittingMeasure_singular_of_deficit_compactness`. Besides the
standing finite-law, semigroup-generation, discreteness, and nonelementarity
hypotheses, its only additional premise is `FuchsianDeficitCompactness`.
This is a proved implication, not a proof of the unrestricted conjecture.

The premise, defined in
[FuchsianDeficitCompactness.lean](Singularity/FuchsianDeficitCompactness.lean),
says that every sequence of group elements has a strict subsequence and a
finite boundary set `Z` with this property: for each open neighborhood `U`
of `Z`, some fixed allowance `R` makes

```text
d_G(1,g_n) - sigma_nu(g_n,xi) <= R
```

hold for almost every `xi` outside `U`, at every sufficiently late time in
the subsequence. The null set may depend on the time. This is now proved
when the ideal limit set is proper or a parabolic exists, in
`FuchsianCuspOrProperLimitSingularity`. For the remaining full-limit-set,
parabolic-free case, the current route uses the structural reduction above
and the independently completed cocompact theorem.

`ExceptionalShadowUniformMass` proves that such subsequential control,
atomlessness, and outer regularity imply uniform almost-full inverse mass.
The actual hitting measure is proved atomless in `FuchsianDeficitCompactness`.
`FuchsianMixedDeficitUniformMass` combines this with uniform absolute
continuity and the visual estimates, supplying positive inverse-mass bounds
for the hitting law and its invariant visual carrier at all sufficiently
large indices. No bounded density is assumed.

The final conditional proof shifts the countable family beyond these
indices, derives all mass and cocycle estimates, transfers the finite
correction bound to the carrier, and applies the checked pathwise rigidity
theorem. The resulting Green upper bound gives singularity. Thus uniform
inverse mass and the final assembly are no longer independent missing
inputs; proving the named compactness premise would finish this route.

## Transferring compactness and deriving its entrance estimate

[BoundaryFactorCocycleBounds.lean](Singularity/BoundaryFactorCocycleBounds.lean)
proves that local cocycle deficit bounds descend through an equivariant
measurable factor carrying the source measure to the target measure. The
proof uses restricted measure domination. It does not equate pointwise
Radon–Nikodym derivatives on fibers.

`BoundaryFactorDeficitCompactness` transfers the finite-exception compactness
property when the factor is continuous: exceptional sets map to finite sets,
and their neighborhoods pull back to open neighborhoods. Neither injectivity
nor finite fibers are required.
[FuchsianDeficitCompactnessOfFactor.lean](Singularity/FuchsianDeficitCompactnessOfFactor.lean)
specializes this to a factor whose pushforward is the actual Fuchsian hitting
law. **An auxiliary boundary, a suitable factor, and compactness upstairs
have not been constructed in the unrestricted setting.**

[FiniteEntranceHarmonicDeficit.lean](Singularity/FiniteEntranceHarmonicDeficit.lean)
proves that every fixed finite entrance set `A` admits a constant `C_A > 0`
such that, for any normalized positive superharmonic function `H`,

```text
H(x) <= sum_(a in A) F_A(x,a) H(a)  implies  H(x) <= C_A G(x,1).
```

The constant is uniform in both `H` and `x`. This uses the finite entrance
Green inequality and positive Green values at the finitely many vertices;
no square-integrability assumption is imposed on `H`. For actual stationary
densities it gives a uniform bound on the Green deficit on every region
admitting the entrance representation.
`FuchsianDeficitFiniteEntrance` proves that such representations, using a
fixed finite set at all sufficiently late times for each exceptional
neighborhood, imply `FuchsianDeficitCompactness`. **The geometric construction
of a suitable family of entrance sets remains missing.** The representation
from the pathwise visit condition is now proved below.

## Entrance representation and finite cusp strips

[BoundaryFirstEntrance.lean](Singularity/BoundaryFirstEntrance.lean) proves
exact joint probabilities for first entrance and a boundary event, first at
a fixed time and then summed over all entrance times. The proof uses finite
prefix/future independence and the checked first-step boundary relation.
`BoundaryFiniteEntranceRepresentation` shows that a boundary event forcing
an almost-sure visit to a finite set `A` gives an exact mixture of the
translated hitting laws from the first entrance vertices. `FiniteTranslateDensity`
passes this identity to the actual densities on the region; no L² assumption
on those densities is needed.

[FuchsianFiniteEntrancePaths.lean](Singularity/FuchsianFiniteEntrancePaths.lean)
applies this to the named Fuchsian boundary map. Its compactness criterion
requires only the actual pathwise visit property, not an assumed density
representation. `FuchsianFiniteSeparatorRegions` derives the visit property
from deterministic regions of group vertices with finite exit sets and the
required control of their orbit closures at the ideal boundary. Constructing
an adequate subsequential family of such regions remains unproved. These
are sufficient conditions, not asserted to be necessary for compactness.

[CuspStripFiniteness.lean](Singularity/CuspStripFiniteness.lean) constructs a
concrete finite separator in normalized cusp geometry. Uniform height bounds
at zero and infinity force a fixed axis-ratio strip into a compact rectangle.
Discreteness then gives finitely many group vertices in the strip. If the
group contains nontrivial parabolic shears fixing these two endpoints, both
height bounds follow internally from the proved parabolic orbit-height theorem.
Thus the existing `finiteJumpStrip` separator is finite in this case.

[ParabolicFixedPointCharts.lean](Singularity/ParabolicFixedPointCharts.lean)
now normalizes a parabolic in any prescribed chart taking infinity to its
fixed point. `ProjectiveCuspStrips` transfers strip finiteness to any two
distinct parabolic fixed points in the original projective group.
`FiniteExitEnlargement` adds one-step predecessors, and
`ProjectiveCuspExitSets` obtains a finite outgoing exit set for the negative
chart half-plane. `ChartBoundaryArcs` proves that its ideal accumulation is
contained in the closed nonpositive arc; convergence to an interior point
of that arc eventually places orbit points on the negative side.

[FuchsianCuspDeficit.lean](Singularity/FuchsianCuspDeficit.lean) combines
these constructions with the actual walk. For each such chart it proves:

- a single finite set is visited almost surely on every opposite-arc
  boundary event, uniformly over starting vertices on the negative side;
- the actual hitting density has an exact finite entrance representation
  on that opposite arc;
- there is a real constant R, independent of g, bounding
  `greenDistance s μ 1 g - stationaryLogCocycle ν g ξ` almost everywhere
  outside the closed nonpositive arc whenever `g⁻¹ • z` is on the negative
  side of the chart.

These local statements have no additional entrance or separation hypothesis.
Selection of enough endpoint pairs is now proved when the ideal limit set
is the whole circle. `IntervalBoundaryCharts` checks the orientation of the
bounded interval arc. `ShrinkingBoundaryCharts` uses endpoint density to
put a closed cusp arc, with its center strictly inside, in any prescribed
ideal neighborhood. `ProjectiveOrbitSubsequences` extracts either a
finite-valued tail or an ideal orbit limit. Entrance at time zero handles
the finite case, and the shrinking charts handle the ideal case. This proves
full deficit compactness and singularity in `FuchsianFullLimitCuspSingularity`.
The later `ProjectiveEndpointHeight`, `ProjectiveEndpointStrips`, and
`DenseStripEndpoints` extend this construction across all limit-set gaps
by allowing ordinary points as endpoints. `FuchsianCuspOrProperLimitSingularity`
therefore covers every parabolic group and every proper ideal limit set.
The remaining first-kind structural implication is stated above.

## Boundary orbit minimality and density of cusp endpoints

`EndpointImageBounds` proves that bounded real images of zero and infinity
bound the Euclidean image of any fixed interior point. `BoundaryOrbitMinimality`
uses this estimate to prove that every nontrivial closed invariant boundary
set contains the actual ideal orbit limit set. Consequently, for a
nonelementary projective group, the closure of every boundary orbit contains
the whole ideal limit set. These statements need neither discreteness nor
finite generation.

`ParabolicFixedPointDensity` constructs fixed points and conjugates of
parabolics and applies this orbit result. `ParabolicIdealLimits` proves that
powers of either sign of nonzero shear approach infinity, transports this to
a prescribed parabolic fixed point, and places every such point in the limit
set. Thus, if the group contains a parabolic, the closure of all its parabolic
fixed points is exactly the ideal orbit limit set. This is relative density;
it does not assert that an infinite-covolume group's limit set is the entire
circle.

The current geometry no longer needs the ideal limit set to fill the circle:
ordinary endpoints supply the missing charts when it is proper.

A standalone extraction of the completed cocompact proof is also available
in the sibling `cocompact-proof` folder. It contains only the cocompact entry
module's local import closure and has its own build and logical audit.

## From Green comparison to quasiconvexity — completed

[QuasigeodesicTracking.lean](Singularity/QuasigeodesicTracking.lean) proves the
geodesic-to-path tracking estimate directly in the hyperbolic plane. For a
finite chain with steps at most `L` and

```text
a * |i-j| - b ≤ dist(p_i,p_j),  a > 0,
```

every point of the segment between its endpoints is within a uniform distance
of a chain vertex. The proof chooses the nearest vertex and combines the
linear distance bound with minimality to obtain exponential decay in the
index. `QuasigeodesicEnvelope.lean` sums the resulting disk-coordinate movement
using the checked exponential lattice estimate. The radius depends only on
`a,b,L`, not on the number of vertices. No abstract Morse lemma is assumed.

[WordGeodesics.lean](Singularity/WordGeodesics.lean) constructs shortest word
chains and proves that every subchain is shortest.
[OrbitWordQuasiconvex.lean](Singularity/OrbitWordQuasiconvex.lean) applies tracking
to these actual orbit chains: a linear lower bound on hyperbolic displacement
in word distance forces quasiconvexity.

[GreenOrbitQuasiconvex.lean](Singularity/GreenOrbitQuasiconvex.lean) combines
this with the spectral Green/word estimate. A radial upper bound

```text
greenDistance(1,g) ≤ c * dist(z,g•z) + C,  c > 0,
```

already forces a quasiconvex orbit. Consequently a discrete nonelementary
group containing a parabolic admits no such bound. This obstruction needs no
finite-index free-subgroup hypothesis.

[FuchsianGreenRigidityReduction.lean](Singularity/FuchsianGreenRigidityReduction.lean)
proves hitting-measure singularity under this upper bound. Its conditional
reduction `fuchsian_singularity_of_green_upper_rigidity` isolates the remaining
analytic step: deriving the bound from nonsingularity. The corresponding
bounded-additive-comparison reduction is also checked. Neither analytic
implication is asserted as an unconditional result.

## Green/word comparison and the parabolic obstruction

[GreenWordComparison.lean](Singularity/GreenWordComparison.lean) now proves,
for the actual possibly nonsymmetric walk, uniform constants `a,b > 0` and
`D ≥ 0` such that

```text
a * wordDistance(x,y) - D ≤ greenDistance(x,y) ≤ b * wordDistance(x,y).
```

Both distances are defined from the actual finite support and Green function.
`JumpDistance.lean` constructs shortest directed jump paths;
`WordDistance.lean` symmetrizes the support and proves the word-distance laws
and comparison with forward path length. `GreenJumpBounds.lean` proves both
exponential Green bounds. `GreenDistance.lean` proves nonnegativity, left
invariance, the directed triangle inequality, and the logarithmic comparison.
No symmetry of Green distance is asserted.

`ParabolicDisplacement.lean` proves logarithmic displacement bounds and
sublinear displacement of parabolic powers at every basepoint.
`ProjectiveParabolic.lean` derives the needed conjugacy from the trace
condition, including negative-trace lifts. The checked theorem
`projective_parabolic_trace_green_obstruction` rules out bounded
Green/hyperbolic comparison when those powers have linear word growth.
[VirtuallyFreeParabolic.lean](Singularity/VirtuallyFreeParabolic.lean) now derives
that word growth whenever the group has a free subgroup of finite index. The
proof uses cyclic reduction in the free group and a checked Schreier retraction
to compare lengths in the subgroup and ambient group; it applies to every
infinite-order element, including those with trivial abelianization.

[StableGreenLength.lean](Singularity/StableGreenLength.lean) defines the stable
Green length and proves convergence of `greenDistance(1,g^n)/n`, nonnegativity,
homogeneity under powers, and vanishing on finite-order elements. The companion
[StableParabolicObstruction.lean](Singularity/StableParabolicObstruction.lean)
proves positivity for every infinite-order element when a finite-index free
subgroup exists. Along a parabolic, for every real `δ`, the normalized discrepancy

```text
(greenDistance(1,g^n) - δ * dist(z,g^n • z)) / n
```

converges to that strictly positive stable length. Thus even sublinear error is
impossible. This still does not infer singularity: the existence of a finite-index
free subgroup from the noncocompact Fuchsian hypotheses and the
nonsingularity-to-comparison implication remain unfinished.

## Newly completed proof chain

| Files | Checked contribution |
| --- | --- |
| `TransverseStrip.lean`, `TransverseMartinVectors.lean` | Move a separator by an ambient hyperbolic isometry while keeping the same random walk. Ordinary Ancona supplies square-summable Green envelopes and strong Martin-vector limits. |
| `GeometricNaimKernel.lean`, `GeometricNaimContinuity.lean` | Construct a positive jointly continuous Naïm kernel on the entire off-diagonal compact boundary, including infinity. Prove convergence along every pair of orbit approaches and agreement with the original strip kernel. |
| `GeometricNaimCovariance.lean` | Prove the exact transformation law with the actual reflected and forward Martin factors. |
| `GeometricNaimCurrent.lean` | Combine covariance with the proved hitting-derivative formulas. Construct the actual invariant, nonzero, locally finite, regular, sigma-finite current, equivalent to the backward-forward hitting product. |
| `NaimCurrentRigidity.lean` | Derive current proportionality to Liouville and uniform visual-density bounds when both hitting marginals are nonsingular. No kernel or covariance assumption remains. |
| `NaimOrbitPairing.lean` | Transport the exact kernel pairing to any enumeration of the strip and prove its real-density-weighted version. |
| `RealHittingMartinDensity.lean` | Prove that `q(u) K(g,u)` is a density of the actual real-chart translated hitting measure. |
| `RealCurrentChart.lean` | Transport current equality to the real plane and the opposite half-lines used by the logarithmic Fourier argument. |
| `HittingOrbitColumns.lean`, `HittingDensityPairing.lean` | Construct analysis operators from the actual hitting laws, identify every cyclic density coordinate on a common full-measure set, and prove the exact scalar pairing including the exponential Jacobian. |
| `NormalizedTwoSidedSingularity.lean` | Apply the checked Fourier contradiction to those actual objects. Both laws cannot be nonsingular when a positive diagonal element is present. |
| `ReflectedHittingTransport.lean`, `CocompactTwoSidedSingularity.lean` | Transport both laws through the coordinate change and discharge the normalization and spectral-gap hypotheses. |
| `SymmetricHittingSingularity.lean` | Identify the reflected law with the forward law under symmetry and deduce singularity of the actual hitting measure. |

The Naïm construction uses ordinary Ancona and Green square summability. It
assumes neither visual-density bounds nor a current. Thus the later use of the
current to derive density bounds does not enter its own construction.

## Completed one-sided rigidity argument

The analytic Hopf argument is now applied to the actual Naïm current. Its
measure and coordinate hypotheses are proved, not assumed in the final theorem.

1. `BoundaryFrameSection.lean`, `FrameStabilizer.lean`, and
   `FrameCoordinates.lean` give a global measurable frame decomposition,
   including endpoints at infinity and both central signs.
2. `CurrentFrameLift.lean`, `FrameFiberHaar.lean`, and
   `CurrentFrameLocalFiniteness.lean` lift currents by Haar measure on the
   signed diagonal fibre. A uniform compact-fibre bound proves local finiteness.
   Measurable section changes do not alter the measure.
3. `GeometricNaimFrameMeasure.lean`, `CompactCosetMeasure.lean`, and
   `GeometricNaimQuotient.lean` construct the actual finite, nonzero quotient
   probability, invariant under every real diagonal-flow time. No visual
   absolute-continuity assumption enters this construction.
4. `LiouvilleFrameHaar.lean` proves that the reference Liouville lift has
   exactly Haar's null sets. `StableFrameSection.lean` gives a section whose
   first row depends only on the forward endpoint. At fixed forward endpoint
   and diagonal fibre, changing the backward endpoint follows a lower horocycle.
5. `StableBoundaryProduct.lean` and `StableFrameMeasureTransfer.lean` use
   Fubini and horocycle saturation to transfer Haar-full measurable basins to
   the current lift, allowing an arbitrary backward marginal and a visually
   absolutely continuous forward marginal. The omitted diagonal is explicitly
   handled using nonatomicity.
6. `OneSidedNaimRigidity.lean` applies this transfer to the previously proved
   Haar average basins. Invariance of the actual Naïm probability identifies
   its integrals with Haar's, proving equality of the two quotient probabilities.
7. `NaimQuotientComparison.lean` transfers this comparison upstairs and then
   to both hitting marginals. `CocompactHittingSingularity.lean` combines it
   with the zero–one law and the two-sided Fourier contradiction to prove
   forward singularity without symmetry.

The earlier analytic modules `ErgodicCesaro.lean`, `StableCesaro.lean`,
`StableProductRigidity.lean`, `CompactActionContraction.lean`,
`CocompactHaarAverages.lean`, and `CocompactStableAverages.lean` supply the
mean-ergodic subsequences, contraction, and actual Haar basins.
`CocompactHorocycleRigidity.lean` also retains a general conditional rigidity
theorem for arbitrary measurable coordinates along the stable fibres.

## Completed projective formulation

`SLTwoProjective.lean` proves that the actual kernel of `SL₂ → PSL₂` is
exactly `{I, -I}` and acts trivially on the boundary and hyperbolic plane.
`ProjectiveActions.lean` descends the actions without choosing representatives.
`ProjectiveSubgroupLift.lean` proves that the full inverse-image subgroup is
discrete, has exactly the same geometric orbits, and preserves cocompactness.

`ProjectiveLiftSupport.lean` lifts every jump with both signs and half its
original weight. Positivity and mass one are proved. The general lemma in
`InvolutiveKernelGeneration.lean` proves semigroup generation of the full
lift, so no group-generation substitution is hidden in this construction.
`ProjectiveWalkProjection.lean` proves equality of the projected one-step
and infinite iid path laws, and equality of every hyperbolic path position.

`ProjectiveHittingMeasure.lean` constructs the measurable boundary selector
from the original projective path, proves its almost-sure convergence, and
identifies its distribution exactly with the lifted hitting law.
`ProjectiveCocompactSingularity.lean` transfers the checked singularity result.
Finally, `ProjectiveNonelementary.lean` supplies the orbit condition from the
finite-orbit definition, and `FuchsianCocompactSingularity.lean` states the
cocompact theorem in the original projective language.

## Established foundations

The source also proves the actual finite and infinite walk laws; nonamenability
and the spectral gap; Green-resolvent/path-sum identification; coercivity and
bounded compression inverse; the exact infinite-separator identity; ordinary
cocompact Ancona; the complete compact geometric Martin identification and
minimality; last-exit identification of hitting derivatives; cocompact
Liouville ergodicity; and the finite-lattice Fourier obstruction and injectivity
of Liouville convolution.

The longer module catalog and earlier milestones are preserved in
[MODULE_HISTORY.md](MODULE_HISTORY.md). That file records historical scope
limits, some of which the modules above now discharge. The former dependency
map is preserved in [DEPENDENCY_HISTORY.md](DEPENDENCY_HISTORY.md); it is not
the current list of gaps.

## Verification

- Lean: `leanprover/lean4:v4.34.0-rc2`.
- Mathlib: `3649549a1e4b19461e912299ca7127d8831b79fa`.
- Dependency lock: `lake-manifest.json`.

Run in this directory:

```sh
python3 verify.py
```

This builds the project, checks declaration-name uniqueness and audit coverage,
asks Lean for the axioms of every theorem and definition, and rejects every
axiom except `propext`, `Classical.choice`, and `Quot.sound`. Its report is
[VERIFICATION.txt](VERIFICATION.txt). The final singularity declarations are
included in this transitive dependency audit.

On this machine, `.lake/packages` links to existing dependencies in
`~/Lean/mymath/.lake/packages`. The source archive excludes those links and all
build products. Elsewhere, install the pinned Lean toolchain, let Lake fetch
the locked dependencies, obtain Mathlib's cache with `lake exe cache get`, and
run the verification script.

## Conventions

The right Markov operator is `P f(x) = Σ μ(g) f(xg)` on complex counting `L²`.
The Green operator is `(I-P)⁻¹`. Its coercivity constant is `1/2`; laziness and
self-adjointness are unnecessary. The strip compression is `i* G i`, distinct
from the Green operator of the walk killed outside the strip. Its inverse has
norm at most `2`.

Mathlib's Fourier transform uses `exp(-2π i x ξ)`, so the Liouville multiplier
is `c * liouvilleMultiplier (2 * π * ξ)` in these coordinates. The Fourier
integral, positivity at all frequencies, and `L²` multiplier identity are
proved.
