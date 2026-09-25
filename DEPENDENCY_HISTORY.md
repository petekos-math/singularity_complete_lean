> Historical snapshot before the global Naïm construction and symmetric cocompact singularity theorem. Statements of unfinished work here may have been superseded. See README.md and DEPENDENCIES.md for current status.

# Obligations remaining for the full theorem

This document is a mathematical dependency map, not a list of assumptions that have
silently been accepted by Lean. None of the missing results below is installed as an
axiom in this project. A successful `lake build` currently verifies only the modules
listed in the README.

The intended conclusion is mutual singularity of the hitting measure `ν` and visual
Lebesgue measure, for a nonelementary discrete Fuchsian group `Γ` and a finitely
supported probability law whose support generates `Γ` as a semigroup. The principal
argument treats the cocompact case; the noncocompact extension uses another theorem.

## 1. Objects and probability

Full geometric boundary convergence and its hitting law are now constructed
under the operator spectral-gap hypothesis, now derived from absence of an
invariant mean. In the cocompact case, the explicit dynamical assumption that
every boundary orbit is infinite now supplies nonamenability and the operator
gap (section 2). The general noncocompact group case remains separate. The compact boundary and infinite-time
path law are constructed. The project now uses Mathlib's actual `SL(2, ℝ)` action on the
upper half-plane and proves covariance of the normalized Poisson measures
under its finite-real-chart boundary formula in `PoissonMeasure.lean`,
`PoissonInversion.lean`, and `PoissonMobius.lean`. Boundary poles are treated as
null sets for absolutely continuous measures. `MobiusMeasureAction.lean` now
proves the a.e. composition law, preservation of absolute continuity, and exact
composition and inverse laws for these pushforward measures. `CompactBoundary.lean`
now constructs the compact real boundary inside the complex sphere, the Borel
and metrizable topology, and the continuous genuine SL(2,ℝ) action, including
poles and infinity. Its equivariant upper-half-plane inclusion is an open
embedding. `ProjectiveInversion.lean` and `ProjectiveMobius.lean` supply the
continuity proofs. `CompactPoissonMeasure.lean` lifts the visual measures to
this full boundary and proves exact covariance. The actual subgroup geometry
still requires discreteness and other explicitly stated hypotheses.

Finite-time laws are now constructed in `WalkKernel.lean` and `FiniteWalkLaw.lean`:
ordered jump words carry the product weights, which define an actual PMF; the
endpoint pushforward has probabilities pₙ(x,y). `rightMarkov_pow_delta` identifies
these probabilities with the coefficients of Pⁿ on counting-measure L². The
reflected-law identity `P* = P_checkμ` is proved in `MarkovAdjoint.lean`.

`InfiniteWalkLaw.lean` now constructs the actual probability measure on
sequences of support-valued jumps using Mathlib's infinite product measure.
It proves independence, the one-coordinate laws, shift invariance, and exact
agreement of every finite-prefix pushforward with `finiteWalkLaw`.
`InfiniteWalkProcess.lean` defines measurable position variables, proves their
first-step recursion and endpoint laws, identifies the Green kernel with the
expected total visits, and derives almost-sure finite visits from the spectral
gap. For a countable group it puts eventual escape from every finite set on one
common full-measure set.

The occupation and finite-set escape results alone do not prove geometric convergence;
the quantitative proof is now supplied by the later modules described below.
`WalkHeadTail.lean` now proves independence of the first jump from the whole
future and the associated product law. `WalkBoundaryLimit.lean` derives the
first-step relation from almost-sure convergence and a continuous equivariant
action. `WalkBoundaryLaw.lean` turns that relation into stationarity.
`WalkLimitConstruction.lean` now constructs a measurable limit version and its
unique law of those path limits (which is stationary) from almost-sure convergence in
a metrizable Borel space. `StationaryQuasiInvariant.lean` derives equivalence of
all translated laws from positive support and semigroup generation.
The actual geometric compactification is now constructed in `CompactBoundary.lean`.
`CompactBoundaryEscape.lean` proves that every limit of an escaping discrete orbit
lies on its geometric boundary. Compactness yields boundary accumulation
subsequences for almost every transient random path. `CompactWalkLimit.lean`
instantiates the probability construction with this concrete geometry and proves
that the resulting stationary law assigns mass one to the boundary. Full
almost-sure convergence is an explicit input to this module; the later
`FuchsianWalkConvergence.lean` now discharges it from the spectral gap.
`CayleyMetric.lean` and `CayleyCompactification.lean` now prove a quantitative
compact-coordinate estimate for bounded hyperbolic jumps. `GeometricPathConvergence.lean`
proves full convergence from summability of the radial exponential weights, or
from eventual positive linear escape. Finite support supplies the jump bound.
`WeightedOccupation.lean` proves the weighted occupation formula and square
summability of Green rows, implying almost-sure path summability for nonnegative
weights bounded by a Green row. `GreenEscapeConvergence.lean` uses the lower Green
distance comparison to prove full geometric convergence and construct the hitting
law without a separate convergence assumption. The gap and comparison remain
explicit inputs. The comparison-based argument cannot be used circularly to establish its own
comparison. The independent argument is now supplied as follows.

`HyperbolicGrid.lean` gives at most 49 exp(4R) coordinate cells of hyperbolic
diameter two covering the radius-R ball. `HyperbolicOrbitGrowth.lean` injects
each group-vertex fiber into the radius-two ball, which is finite by proper
discontinuity, and proves exponential orbit growth with stabilizer multiplicities.
`SpectralEscape.lean` bounds transition probabilities by operator power norms
and applies Borel–Cantelli to slowly growing finite sets.
`FuchsianWalkConvergence.lean` combines these to prove positive linear escape,
summable radial decay, and full compact convergence for every starting vertex
and base point, assuming discreteness, finite support, and the spectral gap.
It constructs the stationary, quasi-invariant geometric hitting law of full
boundary mass under positive semigroup-generating support. This requires
neither cocompactness nor Green comparison. The outstanding input for this
construction is now Fuchsian-group nonamenability in the general case.
`CocompactNonamenable.lean` discharges it for cocompact groups with every boundary
orbit infinite, and constructs the actual hitting law under discreteness.

`RealBoundaryTransport.lean` now transports the supported sphere law to the
compact real projective boundary, preserving stationarity and equivalence of
translates. `RealGeometricHittingLaw.lean` constructs the actual real-projective
limit map. `GeometricHittingMeasure.lean` names its probability law, proves
uniqueness among versions of the same path limit, and instantiates the
Radon–Nikodym harmonic and cocycle identities for that actual law. Thus the
geometric hitting measure is available to the later rigidity and Martin steps;
its existence no longer depends on either of them.

The Markov property for general stopping times and a stopping-time filtration
have not yet been developed here. They are not needed by the now-proved
Martin/hitting identification: `WalkPrefixTail.lean` proves deterministic-time
prefix/future independence, `WalkLastExit.lean` computes last-exit event masses,
and the later finite last-exit modules and dominated convergence identify the
actual boundary derivatives (section 3).

## 2. Spectral gap and Green kernels

The generic nonamenability criterion is now proved in `InvariantMean.lean`:
for positive finite support of total mass one generating the group as a semigroup,
absence of a left-invariant finitely additive probability on all subsets implies
`spectralRadius ℂ (rightMarkov s μ) < 1`. This is the operator spectral radius,
not just the exponential decay rate of return probabilities. No laziness,
symmetry, or norm gap is assumed.

The proof constructs almost invariant L² unit vectors from failure of the gap,
then an actual invariant mean by ultrafilter limits of their squared set masses.
`QuadraticSpectralGap.lean`, `CountingModulus.lean`, and `MarkovEnergy.lean`
justify the operator-to-energy reduction; `AlmostInvariantL2.lean`,
`L2SetMass.lean`, and `L2InvariantMean.lean` prove the limiting construction.
Inversion identifies right and left invariant means.

The free-subgroup obstruction and its boundary-dynamics construction are now
proved. `InvariantMeanTransport.lean` proves that means pass to subgroups by
choosing coset coordinates. `FreeGroupNonamenable.lean` proves the free-group
obstruction using four disjoint first-letter cones. `NorthSouthPingPong.lean`
and `NorthSouthConjugate.lean` construct an injective free-group homomorphism
from large powers of an element and a conjugate with disjoint endpoint pairs.
`FiniteOrbitDisplacement.lean` uses Mathlib's B. H. Neumann lemma to obtain that
conjugate from infinite endpoint orbits. `NorthSouthNonamenable.lean` combines
these into the invariant-mean obstruction.

`DilationNorthSouth.lean` establishes the required uniform boundary dynamics
for the actual positive diagonal matrix. `HyperbolicNonamenable.lean` transports
it under an arbitrary SL(2,ℝ) conjugacy. Thus a subgroup containing a conjugate
of a positive dilation, with infinite orbits of its two endpoints, now has a
proved spectral gap and actual hitting law without a separate nonamenability
or operator assumption.

The diagonal conjugacy is now proved from |tr(g)|>2. The explicit expanding and
contracting roots give a determinant-one eigenbasis after elementary shear
conjugation if needed (`HyperbolicEigenvalues.lean`, `HyperbolicNormalization.lean`,
`HyperbolicTraceNormalization.lean`). `HyperbolicTraceSquare.lean` treats both
signs of trace by squaring. `TraceNonamenable.lean` removes the conjugacy assumption
from the nonamenability, spectral-gap, and hitting-law results.

Hyperbolic-element existence is now proved in the cocompact case provided the
orbit of infinity is infinite. `CocompactSmallRow.lean` constructs a shrinking
lower-row sequence, and `SmallRowHyperbolic.lean` shows that absence of a
hyperbolic trace would force every element to fix infinity.
`CocompactHyperbolic.lean` combines these and constructs the normalized subgroup.
`CocompactNonamenable.lean` derives the full spectral-gap and hitting-law chain
under the explicit dynamical condition that all boundary orbits are infinite.

Still handle the general noncocompact group case and any needed equivalence of
this dynamical hypothesis with the chosen general definition of nonelementarity. No part of these remaining geometric obligations is installed as
an axiom. In particular, the general nonelementary-group theorem is not yet
claimed by the project.

The identity `(I-P)⁻¹ = Σ Pⁿ` is now proved in `GreenSeries.lean`, with convergence
in operator norm derived from spectral radius `< 1`, rather than from `‖P‖ < 1`.
Evaluation on vectors and inner-product coefficients commutes with the sum, and
the scalar coefficient series is proved absolutely convergent.

The path-counting identification is now proved: `CountingL2.lean` constructs the
point masses and continuous coordinate evaluations, and `WalkKernel.lean` proves
`(G δ_y)(x) = Σₙ pₙ(x,y)`, with summability, left invariance, entry bounds, and
the first-step Green equation. `FiniteWalkLaw.lean` identifies pₙ with actual
endpoint probabilities.

`GreenAdjoint.lean` now proves spectral-radius invariance under adjoint,
`G_checkμ=G*`, and `G_checkμ(x,y)=G_μ(y,x)`. The reflected spectral gap follows
from the forward operator gap; it is not an extra hypothesis.

`GreenPositive.lean` now proves reachability by finite words and strict Green
positivity under strictly positive weights on a finite semigroup-generating
support. `GreenHarnack.lean` proves fixed-path comparison and Harnack bounds.
`ReflectedSupport.lean` proves that reflection preserves positivity, total mass,
and semigroup generation, and that finite generation implies countability.
These results justify the canonical nonzero Green normalizers without assuming
symmetry or weakening the generation hypothesis.

`SupportedL2.lean` now models ℓ²(A) as the closed subspace of counting-measure
L²(Γ) supported on A. The inclusion is isometric and its adjoint is proved to
retain precisely the A-coordinates. `EntranceOperator.lean` instantiates the
compressed Green inverse on this space, with norm at most two.

The concrete first-entrance operator is now constructed and its columns identified
with the convergent path sums. `HarmonicUniqueness.lean` proves the ℓ² Dirichlet
uniqueness used for this identification, without a killed-operator gap assumption.
The renewal identity `Gi=FG_A` is checked. `FirstReturn.lean` defines the convergent
first-positive-return path series and proves its operator realization together
with `M_A=I−R_A` and the corresponding coefficient formula.

`KilledWalk.lean` constructs the Green columns of paths avoiding A. Dirichlet
uniqueness identifies their operator as `G−Fi*G` in `GreenSeparator.lean`. If A
meets every allowed finite jump path from x to y, the killed term vanishes and
the full separator factorization follows as a bounded Hilbert-space pairing.
The concrete proof uses this route rather than instantiating the older abstract
block-inverse lemma.

`InfiniteFirstEntrance.lean` now identifies F(x,a) with the probability that the
first visit to A occurs at a. Its proof identifies every finite-time event with
the existing path weight and sums disjoint events. The row sum of F is exactly
the probability of ever visiting A, hence at most one. This infinite-path
first-entrance interpretation is proved; the corresponding positive-return
interpretation and general strong Markov theorem remain unfinished.
The formal separator formula does not require an entrywise absolutely convergent
double matrix sum. Such a stronger expansion would need its own justification if
retained in another presentation of the proof.

## 3. Geometric rigidity and boundary kernels

The first part of the nonsingularity reduction is now proved:
`IndependentShift.lean` and `WalkBoundaryErgodicity.lean` establish the zero–one
property for the actual path and boundary laws. `ErgodicMeasureDichotomy.lean`
uses countable saturation of null sets to derive absolute continuity under
nonsingularity. `GeometricHittingErgodicity.lean` applies this to the constructed
hitting law and the actual visual measure. No invariant-measure hypothesis is
imposed on the hitting law. `CocompactVisualErgodicity.lean` transfers the proved
Liouville ergodicity through endpoint projection and proves equivalence of the
visual and nonsingular hitting measures in the cocompact case.

Still formalize the stronger rigidity input (Kim–Zimmer Theorem 1.9 in the writeup):
uniform upper and lower hitting-density bounds from forward nonsingularity,
including the reflected-law input. Both sharp Green-distance bounds are now
proved from forward visual-density bounds, as described below. Equivalence of measures alone
does not supply these bounds or establish nonsingularity of the reflected law.

There is now a checked conditional route to the uniform density bounds that
uses the current identity. `CompactProductDensity.lean` proves the compact
section argument; `BoundaryCurrentDensity.lean` recovers the product of actual
Radon–Nikodym densities from equality of off-diagonal currents.
`BoundaryCurrentBounds.lean` proves reverse marginal absolute continuity and
common positive lower and finite upper density bounds for positive continuous
kernels. `CocompactHittingBounds.lean` combines this with the already proved
cocompact current comparison, so no separate bounded-density hypothesis is
needed if a positive continuous covariant kernel and absolute continuity of
both marginals are supplied. Nonsingularity of both actual laws supplies those
absolute-continuity inputs. This does not yet provide the original one-sided
nonsingularity reduction: the reflected-law input and the global positive
continuous covariant Naïm kernel remain to be established.

Both halves of the sharp Green comparison are now derived from two-sided visual
bounds. `VisualPoissonComparison.lean` supplies exponential visual domination
and full support; `HittingMartinBounds.lean` identifies and bounds the actual
continuous Martin kernels. `GreenMartinLower.lean` constructs a geodesic tail
past every vertex and uses ordinary Ancona to obtain a uniform reciprocal-Green
lower bound at a Martin point. `GreenVisualLower.lean` combines this with Martin
surjectivity to give the sharp lower estimate and the full comparison, including
the reflected Green kernel. `CocompactGreenComparison.lean` supplies the exact
comparison predicate used downstream. This does not derive the visual bounds
from forward nonsingularity alone.

The upper-bound part was established as follows. `FirstEntranceHarmonic.lean` proves finite-time stopping inequalities
and stationary boundary-measure domination. `GreenFirstHit.lean` proves the
singleton renewal identity `G(x,y)=F(x,y)G(y,y)`. The explicit Poisson-measure
estimate in `PoissonDominationDecay.lean` turns boundary-measure domination
into exponential hyperbolic decay. `GreenVisualUpper.lean` yields
`G(x,y) ≤ (2 b G(e,e)/a) exp(-d(xi,yi))` from `a m_i ≤ ν ≤ b m_i`.
`CocompactGreenUpper.lean` combines this with the proved conditional current
and density results and transfers the upper bound to the reflected Green
kernel. No geometric Martin identification or lower Green bound is used for
this implication. The sharp lower comparison with exp(-d) remains missing;
the original nonsingularity assumption still does not supply the actual
continuous kernel and reflected-law input needed by this alternative route.

A preliminary detour estimate for geometric Martin identification is now
proved in `GeometricDetour.lean`, `KilledGreenDecay.lean`,
`KilledWalkTransport.lean`, and `HyperbolicGreenDetour.lean`. A path avoiding
an open radius-`R` hyperbolic ball and joining endpoints separated by `δ` in
the centered disk has at least `δ exp R/(4 exp L)` jumps. Spectral decay,
with a uniform all-time prefactor, bounds its entire killed Green series
by `A exp(-c exp R)`. The constants are uniform over orbit centers and
endpoints with fixed separation. If the hyperbolic endpoint distance is
at least two, a fixed triangle-excess bound `D` supplies separation
`exp(-D/2)/4`. The bound also implies eventual decay at every prescribed
exponential rate. This uses actual paths and their convergent Green series,
without assuming a Martin or Naïm kernel. The later shrinking-ball construction
now deduces ordinary Ancona comparison along constructed geodesic segments.
Contraction/uniqueness of geometric Green quotients and the continuous Naïm
limit have not been deduced yet.

`CocompactGreenLower.lean` now gives a coarse lower comparison
`G(x,y) ≥ a exp(-b d(xi,yi))`, with `a,b>0`, independently of any current
or nonsingularity assumption. `HyperbolicHarnack.lean` makes the finite-path
comparison uniform at bounded hyperbolic displacement. `MetricChains.lean`
and `HyperbolicChains.lean` construct unit-step chains with at most `3d+5`
steps, and `CocompactOrbitChains.lean` transfers them to the group orbit with
at most `3d+7` bounded jumps and the actual group endpoints. This does not
supply the sharp exponent-one lower bound in the rigidity comparison.

`CocompactRelativeDetour.lean` combines that coarse lower bound with the
absolute detour bound to obtain `G_avoid/G ≤ exp(-K R)` at any prescribed
rate `K`, uniformly under fixed triangle-excess bound and endpoint distance
between `2` and `B R`. The linear distance restriction is still essential
to this detour theorem. The shrinking-ball iteration below now uses it to prove
uniform geodesic Ancona comparison. Geometric Martin uniqueness remains work
to be done; no such conclusion has been introduced as an axiom.

A global comparison with polynomial loss is now proved in
`CocompactPolynomialComparison.lean`: for any fixed triangle-excess bound,
`G(x,y) ≤ H (1+d(xi,yi))^p G(x,u)G(u,y)` with constants independent of
all three vertices. This theorem has no endpoint-distance restriction.
`FiniteEntranceDecomposition.lean` turns the checked operator renewal
formula into the exact finite sum over first-entrance probabilities.
`GreenProductBounds.lean` bounds that sum by the product through the center
and proves the universal lower product inequality. The checked global
Harnack estimate and `CocompactGreenBall.lean` bound the entrance cost by
an exponential in ball radius. A logarithmic radius absorbs the detour
remainder into half the actual Green kernel, leaving only polynomial loss.
The later geodesic Ancona theorem removes the polynomial factor under the
segment-neighborhood condition, now also under arbitrary bounded triangle
excess. The later minimality argument now proves unique geometric Martin
limits and continuity on the finite real chart; the compact Martin modules
extend this to an equivariant homeomorphism of the whole boundary. Full Naïm
limits and the sharp exponent-one Green lower bound remain outstanding.

The finite transfer part of the Ancona iteration is now checked in
`FiniteLastEntrance.lean`, `LocalTransferIteration.lean`,
`EntrancePairTransfer.lean`, and `FiniteEntranceIteration.lean`. The actual
forward first-entry and reflected last-entry maps preserve local inequalities
and decrease the Green product through the target center. Total relative
error at most one half yields a factor-two bound. Local Harnack comparison
supplies the terminal estimate when the left endpoint is near that center.

`GeometricEntranceErrors.lean` supplies a common detour threshold for both
orientations. `GeometricEntranceIteration.lean` proves summability for a
backwards radius schedule and discharges all probabilistic error inputs.
The geometric construction is now checked in `ShrinkingAxisInterval.lean`,
`ShrinkingAxisGeometry.lean`, and `CocompactAxisAncona.lean`. Halving the
longer side contracts total interval length by at least `3/4`. Balls of radius
one four-hundredth of that length preserve explicitly defined endpoint tubes.
`CayleyExcess.lean`, `AxisBallSeparation.lean`, and `AxisBallGeometry.lean`
prove uniform triangle excess at each approximate orbit center; pair distances
are between two and 800 times the radius. The stopping threshold gives the
summable radius schedule and a uniform terminal location bound. All balls
are full finite orbit balls and all first/last-entry kernels are the actual ones.
The terminal Harnack constant is chosen after the stopping threshold.

`HyperbolicAxisNormalization.lean` constructs an oriented axis joining any two
points of the upper half-plane, using explicit rotations and the intermediate
value theorem. `CocompactGeodesicAncona.lean` now proves: for every fixed `K`,
there is `C≥1` such that each pair `x,y` has a unit-speed geodesic line joining
`x i` to `y i`, and every orbit point within `K` of any point of its segment obeys
`G(x,o)G(o,y)/C ≤ G(x,y) ≤ C G(x,o)G(o,y)`. The constant is independent of
all endpoints and segment parameters. This is ordinary Ancona comparison in
the cocompact subcritical setting, without symmetry or a polynomial loss.
`AxisTriangleExcess.lean` now proves that excess at most `D` gives an endpoint
segment point within `D/2+log 4`. `CocompactExcessAncona.lean` consequently
gives the uniform product bound for every bounded-excess triple and every
positively disk-separated endpoint pair. Strong Ancona/contraction estimates
and unique geometric Martin limits are the next analytic obligations.

The functional-analytic part of the strong-Ancona contraction is now checked.
`CountingKernel.lean` and `EntranceRepresentation.lean` prove absolutely
convergent infinite entrance sums and exact boundary representations for L²
harmonic functions. `RelativeGreenEntrance.lean` supplies the decomposition
inside a previously killed domain:
`G_A = G_(A∪B) + F_(A∪B) G_A`, with only `B\A` contributing.
It also proves monotonicity under killing, relative singleton renewal, and the
universal lower product inequality for killed Green kernels.

`HarmonicEntranceComparison.lean` transfers comparison of actual entrance rows
to arbitrary real L² harmonic data nonnegative on the boundary.
`CommonSubtraction.lean` proves the common-removal iteration and its geometric
contraction on nested domains. `KilledGreenSubtraction.lean` instantiates the
kernels with normalized killed Green columns and proves preservation of L²
membership and harmonicity wherever the earlier poles/killing sets are absent.
The contraction remains conditional on uniform two-sided comparisons for the
successive residual functions. These comparisons are not packaged as an axiom
or declared to follow from the global Ancona theorem alone.

`KilledGreenReflection.lean` now proves transposition under reflection by pairing
exterior Green equations. `RelativeLastEntrance.lean` supplies the absolutely
convergent last-entrance identity inside killed domains. `EntranceFinalJump.lean`
and `RelativeExitFlux.lean` combine it with the actual final jump into the boundary:
`F_A(x,a)=F_(A∪B)(x,a)+Σ_b G_A(x,b)q_(A∪B)(a,b)`, with nonnegative reflected
entrance coefficients and a proved finite/infinite sum interchange.
`RelativeBoundaryComparison.lean` uses this identity to transfer relative Green
row comparison to entrance and harmonic-function comparison.

`CoordinateBarrier.lean` proves that a bounded-jump coordinate cannot skip a
closed layer of one-jump width, and a further one-jump gap forces the direct
entrance term to vanish. `RadialCoordinate.lean` proves that `log |z|` is
1-Lipschitz for hyperbolic distance. `RadialBarrier.lean` uses its sublevels and
layers to construct actual semicircular stopping domains and prove interception.
Its harmonic comparison theorem still explicitly assumes relative Green bounds.

`CoordinateExcursion.lean`, `GreenKillingLoss.lean`, and `CoordinateGreenLoss.lean`
now prove an exponential bound on the actual mass lost through killing below
a bounded-jump coordinate, using both endpoint depths. `InteriorKilledGreen.lean`
combines it with the unrestricted local lower bound to prove uniform positive
local killed Green values and local Harnack comparison. `RadialKilledGreen.lean`
specializes these conclusions to the semicircular domains in every chart.

`AxisOrbitChain.lean` constructs short orbit chains retaining a radial depth
bound. `KilledGreenChains.lean` and `CocompactRadialLower.lean` use them to prove
coarse exponential killed Green lower bounds for endpoints in fixed deep axis
tubes, independently of segment length. The corresponding normalizers are
strictly positive. `RadialRelativeDetour.lean` then proves arbitrarily fast
exponential relative detour errors normalized by the killed kernel, for segment
length bounded by a fixed multiple of the ball radius. The fixed tube and depth
conditions are explicit, not removed by the statement.

The fixed-tube restriction is now removed in `RadialGeodesicConvexity.lean`,
`DeepRadialOrbitChain.lean`, `DeepRadialGreenLower.lean`, and
`DeepRadialRelativeDetour.lean`. Radial superlevels are proved geodesically convex;
short orbit chains retain their depth up to the covering radius. This proves
coarse exponential killed Green lower bounds and positivity for all pairs beyond
one fixed radial buffer, and relative detour estimates for all such pairs under
the stated distance/radius and excess conditions.

`RelativePairTransfer.lean` and `RelativeEntranceIteration.lean` now provide the
actual first/last-entrance iteration with the original killing set retained.
The terminal product comparison follows from interior killed Harnack estimates.
`RadialCayleySeparation.lean` proves uniform separation and bounded excess for
entire opposite radial regions, not just axis tubes. `RadialGreenComparison.lean`
uses it to give the ordinary Green product comparison throughout those regions;
it does not claim the corresponding killed Green comparison.

`RelativeGreenProductBounds.lean`, `DeepRadialHarnack.lean`, and
`DeepRadialGreenBall.lean` now prove the finite-ball product estimate inside
the killed domain, with its exact remainder and exponential radius cost.
`DeepRadialPolynomialComparison.lean` proves a polynomial relative product
bound when the intermediate vertex has the stated logarithmic clearance.

`ShrinkingRadialDepth.lean` and `DeepRadialAxisAncona.lean` now construct and
verify the entire shrinking-ball sequence under linear radial clearance.
The actual segment-endpoint theorem gives a uniform Ancona upper constant
when both endpoint depths exceed the killing level by a fixed constant plus
`1/50` of the segment length. Every depth, successor, error, and terminal
condition of that construction is proved. No relative Ancona axiom is used.

An outstanding obligation in the strong-Ancona route is uniform relative comparison for the full barrier layers
without the length-dependent clearance condition. The proved restricted theorem
does not discharge that obligation: arbitrarily distant points along a fixed
barrier need not satisfy it. The nested domains and successive residuals must
then be shown to meet the checked contraction hypotheses. Normalizer positivity
is available whenever the endpoints obey the proved fixed deep-domain condition.
After proving these analytic and geometric inputs, apply the checked
contraction to prove uniqueness and quantitative continuity for actual normalized
Green kernels. The common-subtraction route is guided by §4.2 of the paper below;
its domain comparisons are still mathematical work to be formalized.

The construction is guided by the proof of Theorems 4.1 and 4.3 in
[Gouëzel–Lalley, §4.1](https://www.numdam.org/article/ASENS_2013_4_46_1_131_0.pdf),
but no external theorem is accepted as an axiom.

The initial Martin compactness step is now proved in `MartinCompactness.lean`:
finite Green quotients have positive coordinate lower bounds and finite upper
bounds; every sequence of poles has a pointwise convergent subsequence. Limits
are normalized and positive, and are harmonic when the poles escape each fixed
state. `ReflectedMartin.lean` supplies the reflected result and a common
subsequence for both families.

`MartinBoundary.lean` now constructs the actual abstract Martin compactification
as the closure of the normalized Green columns. The finite-state map is
injective, the closure is compact, and the boundary is precisely the harmonic
part of that closure. Evaluation gives continuous positive normalized harmonic
kernels. `MartinApproximation.lean` isolates finite states, constructs escaping
finite-pole approximations to every abstract boundary point, and proves
nonemptiness when the group is infinite.

`MartinAction.lean` constructs the group action by homeomorphisms on this
boundary and proves the positive normalization cocycle law. `NaimCovariance.lean`
proves covariance of the finite Green quotient and of any existing limit whose
Martin coordinates converge. It does not assume or prove that the normalization
cocycle is a Radon–Nikodym derivative of a hitting measure.

The first quantitative geometric consequences are now proved.
`GreenVanishing.lean` derives vanishing of both Green rows and columns outside
finite sets from their checked square summability. `RayMartinBounds.lean`
proves `1/C ≤ G(e,x_m)H(x_m) ≤ G(e,e)` for every pointwise subsequential
Martin limit along a chosen orbit ray, with a uniform constant. Such limits
therefore grow to infinity along their own ray. `RayMartinSeparation.lean`
uses disk-separated Ancona comparison to show that every limit from a different
finite real direction tends to zero on that ray. `RayMartinClusters.lean`
proves that the sets of all ray subsequential limits are nonempty, belong to
the actual abstract Martin boundary, and are disjoint for distinct finite real
endpoints. The subsequent minimality route now proves uniqueness on each
chosen ray: `RayTailExcess.lean` obtains uniform eventual triangle excess from
monotonicity of distance minus ray time; `RayMartinMinimality.lean` applies
ordinary Ancona and the proved harmonic-cone argument in
`HarmonicMinimality.lean`. `RayMartinUniqueness.lean` proves that each cluster
set is a singleton. `RayMartinConvergence.lean` upgrades this to full pointwise
convergence and constructs an injective map into the actual Martin boundary.
This route does not require the missing relative Ancona comparison.
`BoundaryRadialChart.lean` now supplies radial escape for arbitrary finite
boundary approaches. `BoundaryMartinComparison.lean` uses ordinary Ancona to
dominate every resulting cluster function by the minimal ray function.
`GeometricMartinConvergence.lean` proves uniqueness and full convergence for
all such approaches, including tangential ones. `GeometricMartinContinuity.lean`
proves continuity of the map into the actual Martin boundary on the real chart.
`GeometricMartinCovariance.lean` intertwines it with the actual Martin action
whenever the source and image boundary coordinates are finite. No derivative
of the hitting law is assumed or identified by these statements.
`CompactMartinChart.lean` uses an infinite orbit of infinity to choose actual
group elements moving boundary points into finite charts. `CompactMartinMap.lean`
constructs the full map and proves arbitrary-approach convergence and chart
independence. `CompactMartinContinuity.lean` proves continuity at every compact
boundary point. `GeometricMartinHomeomorph.lean` proves injectivity and
surjectivity onto the actual Martin boundary and bundles the homeomorphism.
`CompactMartinCovariance.lean` proves equivariance without excluded endpoints.
`CompactMartinMinimality.lean` proves every abstract boundary point is minimal.
Thus the cocompact geometric Martin identification is now complete under the
stated infinite-orbit hypothesis. The global off-diagonal Naïm limit remains
outstanding; the opposite-side chart is now proved as detailed below. The hitting-measure derivative identification is now proved by the
last-exit argument described next.

`FiniteLastExitLaw.lean` constructs actual finite last-exit probabilities and
proves their exact Martin density under change of starting point.
`FiniteLastExitVertex.lean` realizes these laws on the original path space.
`LastExitConvergence.lean` proves convergence along finite exhaustions, and
`GeometricLastExitConvergence.lean` identifies the corresponding geometric and
Martin limits with the actual hitting point. `LastExitExpectation.lean` proves
the finite integral identity. `HittingMartinIntegral.lean` passes it to boundary
expectations using the uniform coordinate Harnack bound for domination.
`HittingMartinDensity.lean` proves equality of the resulting measures and then
identifies both actual RN derivative versions. `HittingMartinIdentification.lean`
extends the formula to every geometric base point, all starting-state coordinates
on one full-measure set, and minimality of the resulting harmonic functions.
These results use the same cocompact and infinite-orbit hypotheses; the desired
identification is not assumed and last-exit times are not used as stopping times.

`NaimAnconaBounds.lean` gives the universal lower bound `1/G(e,e)` on the
finite Naïm quotient and a finite upper bound for separated pairs. Distinct disk
limits consequently have positive finite subsequential quotient limits.
`CayleyRealBoundary.lean` and `GeometricNaimSubsequence.lean` apply this to
arbitrary approaches to distinct finite real boundary coordinates. On the
concrete orbit rays, one subsequence also gives positive normalized harmonic
forward/reflected Martin limits. No current or density assumption is used.
The full Naïm limit, independence from the approach, and continuity remain
unproved. Martin kernels themselves are now identified with the actual
hitting-measure Radon–Nikodym derivatives as described above.

The opposite-side construction is now proved without rigidity inputs.
`StripBoundarySeparation.lean` gives uniform Cayley separation from the entire
axis strip for every finite nonzero boundary approach. `StripGreenDomination.lean`
uses ordinary Ancona to bound the normalized strip row and column by fixed
multiples of the base Green row and column. Spectral-gap square summability
supplies the dominating envelopes. `StripMartinVectors.lean` proves actual
strong limits with reflected/forward Martin coordinates. `StripNaimKernel.lean`
defines their compressed-inverse pairing and proves full real and complex
Naïm convergence along every pair of sequences approaching `ξ<0<η`, reality,
and the positive lower bound `1/G(1,1)`. `StripNaimContinuity.lean` proves joint
continuity on that chart. There is no current, visual-density, or sharp
Green-distance assumption in these statements.

Still extend this kernel across the whole off-diagonal compact boundary and
prove chart compatibility and covariance. An available route is to transport
separating strips by hyperbolic coordinate changes, retaining the same Green
normalizers; neither that transport nor global compatibility is assumed here.
Arbitrary-approach Martin convergence and the equivariant homeomorphism of the
whole compact geometric boundary are now proved, as detailed above. The
geometric hitting laws are constructed under the spectral gap, and their
derivatives are now identified with the Martin kernels in the cocompact case.
`StationaryDensity.lean` proves reconstruction, positivity, normalized
harmonicity, and the cocycle law for actual Radon–Nikodym derivatives of a
stationary measure with positive semigroup-generating support. The identification
with the actual Martin coordinates is supplied by `HittingMartinDensity.lean`
and `HittingMartinIdentification.lean`. `WeightedCurrent.lean`
now proves the change-of-variables implication from those formulas and kernel
covariance to weighted-product invariance. `MartinCurrent.lean` instantiates
this implication for the actual forward and reflected Martin boundaries, with
all unproved inputs explicit. The convention is `g_*ν = c(g⁻¹,·) ν`.
The geometric pair-space measure construction is now in `BoundaryPairs.lean`:
ordered distinct endpoints form a locally compact metrizable open subspace,
with the actual diagonal action. Nonatomic probability marginals give a
probability reference measure there. Real weights give sigma-finite currents;
a continuous weight gives local finiteness and regularity, and a positive
weight gives nonzero mass. `BoundaryPairInvariance.lean` identifies the embedded
current with the full weighted product and transfers invariance to pair space.
`StationaryCurrent.lean` proves that the actual stationary Radon–Nikodym
identities suffice for covariance cancellation, including their a.e. positivity.
`GeometricKernelCurrent.lean` instantiates this construction with the actual
reflected and forward hitting laws. The reflected law inherits all its walk
hypotheses, including the spectral gap.

Still construct the full Naïm kernel and prove its continuity, positivity, and
covariance in the actual hitting derivatives. The current construction does
not establish any of those kernel inputs. The conditional Radon and invariance
results must be applied only after those inputs have been proved.

Cocompact Liouville ergodicity is now proved. Still establish the remaining
hitting-measure and kernel hypotheses of the current comparison. `CurrentComparison.lean` now proves that equivalent
marginals and positive measurable kernels give equivalent weighted-product
currents. It also proves that positive real weights preserve nonzero mass and
that scalar equality of currents gives the a.e. scalar identity of their real
densities. The actual hitting-measure equivalence and geometric kernel properties
still have to be supplied.
**Invariance alone does not imply identification with Liouville measure**.
`ErgodicCurrent.lean` now proves the general implication: for a group-ergodic
sigma-finite reference measure, every absolutely continuous invariant
sigma-finite measure is a scalar multiple; for nonzero measures the scalar is
positive and finite. This result allows infinite total mass. For the actual hitting marginals, `GeometricKernelCurrent.lean` now supplies
sigma-finiteness and, conditional on continuity and positivity of the kernel,
local finiteness, regularity, and nonzero mass. Covariance supplies invariance;
absolute continuity of the hitting marginals supplies current comparison.
The outstanding inputs are the actual Naïm kernel and its proved properties,
and the rigidity conclusion for the hitting marginals.

The Mautner route to cocompact Liouville ergodicity is now proved.
`Mautner.lean` establishes the contraction argument for continuous isometric
actions. `ShearContraction.lean` supplies the actual upper and lower SL(2,ℝ)
conjugation limits, and `MautnerSLTwo.lean` combines them with transvection
generation. `MautnerDomainAction.lean` handles the opposite multiplication in
precomposition. `MautnerErgodicity.lean` applies this to actual Lp spaces and
L² indicators, upgrading diagonal invariance to full-group invariance modulo
null sets. Thus an ergodic continuous SL(2,ℝ) action on a finite regular
measure space has ergodic positive diagonal time maps.

`QuotientErgodicity.lean` proves the full-group ergodicity hypothesis for Haar
quotients by lifting null sets through a fundamental domain. `SLTwoHaar.lean`
derives unimodularity from perfection of SL(2,ℝ). Consequently,
`QuotientDilationErgodicity.lean` proves diagonal-time ergodicity on the finite
quotient measure constructed from a finite Haar fundamental domain for a
discrete subgroup. It derives countability, quotient separation, and measure
regularity instead of assuming them in that final theorem.

The finite-domain obligation is now discharged for the original cocompact
surface hypothesis. `MeasurableTransversal.lean` and `CompactTransversal.lean`
construct a measurable representative in every fiber from finitely many local
sheets, contained in a compact set. `CompactFundamentalDomain.lean` turns this
into a finite-mass fundamental domain for a discrete subgroup with compact
coset quotient. `CocompactGroupQuotient.lean` derives that compactness from
compactness of Γ\ℍ using the proper SL(2,ℝ) orbit map. `CocompactHaarMeasure.lean`
constructs the actual finite nonzero Haar quotient measure and proves its
invariance and positive-diagonal-time ergodicity.

The Haar-to-Liouville measure-class identification is also proved.
`BoundaryPairTransitivity.lean` supplies explicit matrices for every distinct
ordered pair, including infinity; `BoundaryActionMeasurable.lean` proves joint
measurability for the full group. `HomogeneousMeasureClass.lean` uses Fubini
and transitivity to identify orbit-pushforward null sets with those of any
nonzero invariant sigma-finite measure. `LiouvilleHaarMeasureClass.lean`
applies this to the actual Liouville current and the inverse-frame endpoint
map, proving the required dilation invariance and right-multiplication rule.

The final measurable descent and ergodicity transfer are now proved.
`InvariantSetDescent.lean` replaces an almost-invariant set for a countable
group by its exactly invariant measurable core, equal modulo null sets, and
descends this core to the quotient sigma algebra. `QuotientFlowDuality.lean`
transports the descended set's almost-invariance to the quotient time map,
uses its ergodicity, and lifts nullness or conullness back through the endpoint
measure-class correspondence. `CocompactLiouvilleErgodicity.lean` instantiates
this with the actual objects and proves
`ErgodicSMul Γ BoundaryPair compactLiouvilleCurrent` from discreteness and
compactness of Γ\ℍ alone. Cocompact Liouville ergodicity is no longer a missing
input.

The Liouville reference current is now constructed independently of these
missing inputs. `BoundaryCircle.lean` gives the continuous injective compact
Cayley circle coordinate. `LiouvilleBoundaryKernel.lean` defines the positive
continuous kernel 4π²/dist(Cξ,Cη)². `LiouvilleCurrent.lean` weights the actual
two visual probabilities by it on distinct endpoints, proves local finiteness,
regularity, sigma-finiteness and nonzero mass, and identifies the chart measure
exactly with dx dy/(x−y)². `LiouvilleTransformations.lean` proves the elementary
translation, dilation and inversion invariances using the established Lebesgue
Jacobians. `LiouvilleMobius.lean` proves invariance for every SL(2,ℝ) matrix;
`LiouvilleInvariance.lean` transfers this to the compact endpoint space and all
subgroups. Reference-current construction and invariance are therefore no
longer hypotheses. Ergodicity of the cocompact lattice action is now also proved.

`GeometricLiouvilleComparison.lean` combines this concrete reference with the
actual hitting marginals and the existing ergodic uniqueness theorem. It gives
a positive finite scalar conditional on ergodicity, marginal absolute
continuity, and positive measurable kernel covariance. The new cocompact
specialization in `CocompactCurrentComparison.lean` discharges ergodicity using
its proved geometric theorem. It still does not discharge the rigidity theorem,
full Naïm limit, or Martin identification.

These specialized results were not located in the installed Mathlib source during
this implementation. This is not a claim that no formalization exists elsewhere.

## 4. Periodic separator and boundary limit

The periodic separator is now constructed for an actual discrete subgroup of
`SL(2, ℝ)` containing a normalized diagonal element `a` with parameter `τ > 0`.
`PeriodicStrip.lean` uses the dilation-invariant coordinate strip
`|re(z)/im(z)| ≤ R`, proves it has bounded distance from the vertical axis,
and places its normalized height band in a compact rectangle. Mathlib's proper
discontinuity theorem for discrete subgroups then proves finiteness of the
canonical group representatives, retaining all finite-stabilizer multiplicities.

`StripOrbits.lean` proves uniqueness in the half-open height band and constructs
an actual bijection `(n,j) ↦ a^n b_j` onto the strip vertices. It derives the finite
disjoint cyclic decomposition. `StripSeparation.lean` proves that radius
`R = sinh(L/2)+1` prevents jumps of length at most `L` from crossing opposite
exterior sides, and derives `SeparatesJumpPaths` for the recursive path model.
`GeometricStrip.lean` chooses `L` from the finite jump lengths, proves that the
identity lies in the strip based at `i`, and gives the complete finite nonempty
cyclic decomposition together with path separation.

This coordinate strip replaces the exact distance tube in the informal proof.
Its required bounded-width, periodicity, finite-quotient, and separation properties
are all proved. Diagonal conjugacy is now constructed from a hyperbolic-trace
element, including either trace sign by squaring. `ConjugateSubgroup.lean` defines
the actual conjugated subgroup and proves its group isomorphism, homeomorphism,
discreteness, equivariance of both actions, and preservation of infinite boundary
orbits. `ConjugateCocompact.lean` proves preservation of compactness of the orbit
quotient by transporting a compact cover. `CocompactHyperbolic.lean` now supplies
the initial hyperbolic trace from cocompactness and an infinite orbit of infinity;
its existence in the general noncocompact case remains separate.

The supported Hilbert space is identified with sequence ℓ² in
`SupportedCoordinates.lean`. `GeometricGreen.lean` now applies the separator
pairing both in the supported Hilbert space and in the constructed cyclic
coordinates; path separation and enumeration are no longer independent inputs
in these versions. The operator spectral gap remains a hypothesis.
`OrbitGreenBoundary.lean` transports the actual compressed inverse, preserving
its pairing and its norm bound ≤2. The reflected conventions are checked in
`GreenAdjoint.lean` and `GreenBoundary.lean`.

The uniform bounds now follow from the distance comparison and ray approaches.
`VisualPoissonRay.lean` constructs the Möbius image of a vertical ray starting
at i, defines the visual Poisson kernel, proves its usual formula, and derives
`exp(t - d(r_ξ(t),w)) ≤ P_w(ξ)`. A point within distance D of the ray satisfies
the corresponding estimate with factor `exp(2D)`.
`VisualPoissonDecay.lean` proves `P_(a^n w)(ξ) ≤ C_(ξ,w) exp(-τ|n|)` for every
finite nonzero ξ, with an explicit constant and square summability over finitely
many orbits. `GreenPoissonBounds.lean` combines these facts with the explicit
`GreenDistanceComparison` hypothesis to derive the actual normalized row and
column envelopes. That comparison is an unresolved rigidity input, not an axiom.

`GeometricBoundaryLimit.lean` combines the estimates with the actual finite
strip enumeration and separator: pointwise normalized Green-coordinate limits
then imply strong ℓ² convergence and convergence of the actual scalar Green
pairing. In this theorem neither separation nor an independent envelope is
assumed. Its remaining inputs are the operator spectral gap, initial Green
comparison, diagonal subgroup element, bounded-distance ray approaches,
eventual opposite sides, and pointwise limits.

Those ray and side inputs are now supplied from actual compactness of the orbit
quotient in `CocompactRayApproximation.lean`. The proof uses the open quotient
map and a finite subcover to construct a compact covering set. Its bounded
distance from i gives one positive approximation radius for every point of ℍ.
The resulting `cocompactRaySequence` chooses group vertices near integer ray
times. `BoundaryRayApproach.lean` proves the explicit bound
`dist_ℂ(z,ξ) ≤ (1+ξ²) exp(D-t)`, hence convergence to ξ, eventual sign,
eventual avoidance of every fixed ratio strip for ξ ≠ 0, and escape to infinite
hyperbolic distance. Each fixed group state is eventually avoided.

`CocompactBoundaryLimit.lean` supplies these constructed sequences to the actual
strip theorem. Its full-sequence version still assumes pointwise boundary
coordinates. Its `cocompactStrip_naim_subsequence` combines the proved Martin
compactness with the geometric bounds and obtains a convergent Naïm-quotient
subsequence without any coordinate-limit, ray-approximation, separator, or
envelope hypotheses. It still requires compact quotient, discrete subgroup,
a normalized diagonal element, a positive finite semigroup-generating law,
the spectral gap, and the initial Green-distance comparison. It does not prove
uniqueness, independence of the choices, or the full off-diagonal boundary limit.

The analytic implication from pointwise convergence and a square-summable
envelope to strong `ℓ²` convergence is now proved in `DominatedLimit.lean`, including
construction of the limit and passage to the bounded-operator pairing. Summability
of the one-dimensional exponential envelope and its square is proved in
`ExponentialLattice.lean`. `CountingSequence.lean` transfers dominated convergence
to counting-measure L² and the supported subspace used by the actual Green
operators. `GreenBoundary.lean` constructs the normalized Green rows and columns,
proves the normalized separator identity, and derives its boundary limit from
explicit coordinate limits and square-summable envelopes.

`orbitGreen_boundary_limit` now applies to scalar Green quotients in the orbit
coordinates, deriving summability from finite families of exponential envelopes.
It constructs the limit vectors, proves their strong convergence, and identifies
the scalar boundary limit through the transported compressed inverse.

`NaimSubsequence.lean` now removes the coordinate-limit hypothesis for a
subsequential version: the proved simultaneous Martin compactness supplies the
limits, the exponential envelopes imply strong convergence, and the canonical
ratio G(x,y)/(G(x,o)G(o,y)) converges along the selected subsequence to the actual
Green pairing.

Still derive the initial visual-density bounds from forward nonsingularity;
they now imply the full sharp Green-distance comparison.
The group ray approximations, their eventual sides, and full geometric Martin
identification are now proved under the cocompact hypotheses. The coordinate
limits are also identified with actual hitting derivatives. The old subsequential
Naïm result alone does not establish the full two-boundary-variable limit.
`CocompactStripMartinLimit.lean` now instantiates its coordinate limits using
the actual Martin kernels and supplies Green comparison from visual bounds.
The newer `StripNaimKernel.lean` removes visual bounds and proves full arbitrary-
approach limits directly on the opposite-side chart; global extension remains.

## 5. Analysis operators and the current factorization

The actual geometric hitting law is now constructed on the real projective
boundary under the spectral gap. Absolute continuity under nonsingularity is now
proved, and in the cocompact case equivalence with visual measure is proved.
The initial uniform bounded-density conclusion remains to be established.
`FiniteBoundaryChart.lean` now transports a compact Poisson bound to the real
chart, proving zero mass at infinity, exact reconstruction, preservation of the
probability law, the real Poisson density estimate, and the compatibility of
all Möbius pushforwards. The bound is still an input, not derived from
nonsingularity. `BoundaryMeasureClasses.lean` identifies compact visual
singularity with real-chart Lebesgue singularity even without assuming zero
mass at infinity. Thus changing boundary models is no longer a missing input. The transport from an initial bound to all Möbius translates is now
proved: `PoissonDomination.lean` takes `ν ≤ B m_z`, proves
`g_*ν ≤ B m_(g·z)`, and derives the real Radon–Nikodym Poisson bound.
`PoissonMeasure.lean` proves normalization and equivalence with Lebesgue measure;
`PoissonInversion.lean` and `PoissonMobius.lean` prove the full transformation
law, including the exceptional real-chart pole. `MobiusBoundaryAnalysis.lean`
constructs the analysis family from the resulting actual Möbius pushforward
measures, with no independent row-by-row Poisson-bound assumptions.

`LogBoundaryDensity.lean` now defines both logarithmic densities, proves their
measure identities and independence of representatives a.e., and derives
integrability and mass ≤1 from the original boundary-measure mass bound.
It proves the density formula for dilation pushforwards and its logarithmic
translation law. `DilationOrbit.lean` now proves this action and the exact
orbit-measure relation for the explicit diagonal subgroup. `MobiusOrbitDensity.lean`
identifies its logarithmic orbit densities, analysis coordinates, and ℓ² columns
simultaneously a.e. `CanonicalOrbitDensity.lean` supplies canonical representatives
for every actual pushforward and a nonzero L² annihilator for the whole finite-family
cyclic orbit. The actual strip enumeration is now constructed in `StripOrbits.lean`. Transport of the named random-walk law under subgroup conjugation is now proved
in `NormalizedHittingLaw.lean`. Identification of the Martin boundary limits with
these actual hitting densities remains.

`PoissonDecay.lean` supplies an integrable exponential envelope for the two
logarithmic Poisson profiles. `BoundaryDensityAnalysis.lean` now derives all the
logarithmic integrability, mass, and decay conditions from the real-boundary
densities and constructs the bounded analysis operator and its nonzero kernel.
`BoundaryMeasureAnalysis.lean` goes further: a.e. Poisson bounds for the real
Radon–Nikodym derivatives yield canonical pointwise bounded representatives,
proved to represent the original measures. The operator is constructed from
the boundary measures themselves, and its coordinates agree with any density
representatives of the dilated orbit measures. No preferred representatives,
logarithmic integrability bounds, or logarithmic mass estimates are assumed in
this construction. The initial bounded-density rigidity conclusion for the
actual hitting measures is still unproved; its transport by Möbius maps is now
verified. No equality of hitting measures with Poisson measures is asserted.

The weighted Cauchy–Schwarz proof, uniform overlap bound for exponentially
decaying lattice translates, `L² → ℓ²` map, coordinate formula, and operator-norm
bound are now checked in `WeightedCauchySchwarz.lean`, `AnalysisOperator.lean`,
`ExponentialLattice.lean`, and `TranslatedAnalysis.lean`.

The measure-theoretic implication from a current comparison to the logarithmic
scalar density identity is now proved in `CurrentComparison.lean` and
`LogBoundaryMeasure.lean`. The latter proves the actual exponential Jacobian
pushforward formulas on the two half-lines, their product formula, null-set
pullback, and the identity
`exp(s) exp(t)/(exp(s)+exp(t))² = 1/(4 cosh²((s-t)/2))`.
It does not assume the coordinate change as an extra hypothesis.

Still obtain the geometric current comparison and identify its logarithmic
density with the pairing of the actual strip density vectors. The analytic
passage to `C = H₋* M_A H₊` is checked in `DensityVector.lean` and
`KernelFactorization.lean`: the density columns are bounded strongly measurable
ℓ² vectors, analysis agrees with their Bochner integral on L¹∩L², and the paired
kernel is absolutely integrable on this test class. Equality of the scalar kernels
a.e. implies equality of the bounded operators by density of Schwartz functions.
The convolution side is identified with its actual cosh-kernel pairing in
`liouvilleConvolution_inner_cosh`.

The theorem `impossible_liouville_kernel_identity` combines this implication with
the proved nontrivial kernel of the lattice analysis operator and injectivity of
Liouville convolution. It does not assume an operator factorization. It still
assumes the scalar kernel identity and base-density bounds, which must be obtained
from the geometric hitting measures and current comparison.

`CurrentFactorization.lean` now proves `impossible_liouville_current_identity`:
a measure-level current comparison plus the logarithmic boundary pairing and
lattice-density hypotheses implies the same analytic contradiction. The cosh
kernel identity is derived using the proved Jacobian and measure-density
uniqueness, instead of being an additional assumption in this version.

`BoundaryMeasureContradiction.lean` now proves
`impossible_boundaryMeasure_current_identity`, combining this current route
with the analysis family built from boundary measures. The remaining inputs
are the actual boundary subprobability measures with absolute continuity and
a.e. Poisson bounds, the positive lattice spacing, and the geometric current
comparison and strip-pairing representation. This conditional contradiction
does not construct hitting measures or establish the geometric hypotheses.

## 6. Completed finite-translate and Fourier-multiplier arguments

The actual `N × (N+1)` frequency matrix is now defined from Mathlib's L² Fourier
transform in `FrequencyKernel.lean`. Its entries are proved measurable, and
`exists_frequency_unit_kernel` proves a measurable unit vector in its kernel at
every frequency. No measurable-choice hypothesis is assumed.

The proof uses the Cesàro averages of the contraction
`I − (1 + ‖B‖²)⁻¹ B*B`, whose fixed space is `ker B`. The mean ergodic theorem
supplies convergence to the orthogonal projection. A first-nonzero choice from
projected vectors in a fixed countable dense sequence is measurably normalized.
This replaces the writeup's resolvent-regularization and column-threshold argument.
The original regularized-inverse formula itself has not been formalized.

The following steps are now complete:

- `FiniteBand.lean` constructs the scalar finite-band L² function and proves its
  exact squared norm is `q > 0`.
- `BandOrthogonality.lean` justifies the cell integrals and matrix cancellation.
- `FourierTranslation.lean` proves translation covariance on all of L² by density
  of Schwartz functions, and checks the phase identity across frequency cells.
- `LatticeObstruction.lean` proves that the lattice translates of any finite
  family of L² functions have a proper closed linear span.
- `AnalysisKernel.lean` proves `ker H ≠ {0}` for the actual constructed bounded
  analysis operator, under the base-profile hypotheses. It also proves the
  resulting contradiction if an injective operator factors through H.

Mathlib uses cycles per unit length. The band spacing `q = 1/τ` and phase identity
for translations by `nτ` are now checked in this convention.

The Liouville multiplier and convolution operator are now also fully identified:

- `GammaDensity.lean` proves `Fourier(g)(ξ) = Gamma(1 - 2πiξ)` for
  `g(t) = exp(t) exp(-exp(t))`, with integrability and mass one.
- `LiouvilleFourier.lean` proves the autocorrelation identity, the cosh formula,
  and the exact Fourier integral `πω/sinh(πω)` (value one at zero), where `ω = 2πξ`.
- `L2Convolution.lean` constructs the bounded Bochner convolution operator.
- `ConvolutionMultiplier.lean` proves its multiplier identity on all of L² and
  the resulting injectivity criterion, including the Fubini justification.
- `ConvolutionKernel.lean` proves the weak physical-space kernel formula with
  absolute-integrability estimates for arbitrary L² inputs.
- `LiouvilleOperator.lean` proves injectivity of the actual Liouville convolution
  and the contradiction with factorization through the constructed analysis operator.

Neither injectivity of the Liouville convolution nor nontriviality of the analysis
kernel remains an assumed input. `KernelFactorization.lean` now derives the
operator factorization and contradiction from an a.e. scalar kernel identity.
This scalar identity and the geometric base-density hypotheses remain inputs;
they must be derived from the boundary/current statements in sections 3–5.

## 7. Assembly and noncocompact extension

Apply the proved analytic contradiction to the actual objects and discharge
the nonsingularity assumption. `geometricHittingMeasure` now names the actual
constructed law, and `geometricHittingMeasure_singularity_iff` connects its
`MeasureTheory.Measure.MutuallySingular` conclusion against the compact visual
measure to the real-chart Lebesgue conclusion. This equivalence does not prove
either side. The missing rigidity and current inputs must still be discharged.

For the noncocompact extension, formalize the group-theoretic reduction and the
additional rigidity/singularity result cited in the writeup. No part of this
extension is currently formalized here.

A complete verification requires these obligations to be proved or imported from
kernel-checked libraries. Replacing them with axioms, `sorry`, a structure containing
the final conclusion, or an assumed current factorization is not a complete
formalization of the singularity proof.

The coordinate change now identifies the actual named hitting measures.
`WalkTransport.lean` proves transport of the infinite product path law and every
finite-time position. `HittingConjugacy.lean` uses uniqueness of compact limits to
identify the boundary maps almost surely and their hitting laws exactly.
`WalkIsomorphism.lean` transports all jump-law conditions and nonamenability,
so `NormalizedHittingLaw.lean` constructs the law on B⁻¹ΓB without an extra
spectral-gap assumption. Its hitting measure is the B⁻¹-pushforward of the
original law. Visual covariance then proves equivalence of the singularity
conclusions. `HittingBasepoint.lean` also removes dependence on the base point
and identifies the boundary law from every starting vertex. None of these
identifications supplies the missing rigidity or current statements.

`MaximalAtoms.lean` and `StationaryAtoms.lean` now prove that finite stationary
measures have zero singleton masses when all group orbits are infinite. The
proof uses the maximal-atom argument with semigroup generation, not an assumed
absolute-continuity statement. `HittingMeasureAtoms.lean` applies this to the
actual geometric hitting law. Zero mass at infinity, exact real-chart
reconstruction, and absence of point masses in the real chart are now available
without the rigidity input. It also proves zero product mass on the compact
boundary diagonal. This does not yet construct or identify the Naïm current.
