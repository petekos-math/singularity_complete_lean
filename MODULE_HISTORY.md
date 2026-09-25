> The full theorem is now proved in FuchsianSingularity.lean. The historical entries below retain earlier descriptions of unfinished work; consult README.md for the final status.

> Historical snapshot before the global Naïm construction and symmetric cocompact singularity theorem. Statements of unfinished work here may have been superseded. See README.md and DEPENDENCIES.md for current status.

# Singularity of harmonic measure: Lean formalization in progress

**This is a compiled partial formalization, not a Lean proof of the singularity theorem.**
There is no declaration asserting singularity of the hitting measure. The unfinished
mathematics is listed in [DEPENDENCIES.md](DEPENDENCIES.md), rather than introduced
as axioms or filled with `sorry`.

The intended target is the full argument in
`../outputs/singularity-conjecture-proof.tex`, with the subsequent correction that
Green coercivity has constant `1/2` and does not require laziness. The main target
assumes finite support and generation as a **semigroup**. A weakening to generation
as a group is not included.

The actual hitting-measure derivatives are now identified with the constructed
Martin kernels in the cocompact case. For every group element `x`,
`x_*ν = K(x,·)ν`; all real derivative coordinates agree with their Martin
coordinates on one common full-measure set. Their minimality is also proved.
This uses the existing discreteness, cocompactness, positive finite probability
weights, semigroup generation, spectral gap, and infinite-orbit-of-infinity
hypotheses. The proof uses actual last-exit distributions and dominated convergence.
A positive jointly continuous Naïm kernel is now constructed for finite endpoints
`ξ < 0 < η`, with convergence along every pair of approaches and the exact
compressed-inverse pairing. This construction uses ordinary Ancona and Green
square summability, without visual-density or rigidity assumptions. Global
extension across the whole off-diagonal boundary remains unfinished.

The measure-theoretic part proves the zero–one property for the actual hitting
measure and that nonsingularity against visual measure implies absolute continuity.
In the cocompact case, visual ergodicity follows from the proved Liouville ergodicity,
and the two measures are equivalent. A further checked argument now derives
uniform density bounds from a positive continuous covariant current kernel and
absolute continuity of both hitting marginals. The global kernel construction
and the reflected-law input from forward nonsingularity are still missing.
Both sharp Green estimates are now derived from two-sided visual measure bounds:
first-hit domination gives the upper bound, and the actual Martin identification
combined with Ancona gives the lower bound. The same constant works for the
reflected Green kernel by transposition.

A geometric detour estimate is now also checked directly from finite paths and
the spectral gap. For a fixed positive disk separation of endpoints, paths
avoiding a hyperbolic ball of radius `R` have Green mass at most
`A exp(-c exp R)`, uniformly in its orbit center. A bounded triangle excess gives
the required disk separation. This estimate uses neither the missing Naïm kernel
nor visual-density bounds. It is a preliminary step toward Ancona inequalities,
not the geometric Martin-boundary identification itself.

The cocompact case now also has a coarse exponential lower bound
`G(x,y) ≥ a exp(-b d(xi,yi))`, with positive constants and an unspecified
exponent `b`. Its proof uses constructed short chains in the upper half-plane,
cocompact orbit approximation, and uniform local Harnack comparison. Combining
it with the detour estimate gives a relative bound `G_avoid/G ≤ exp(-K R)`
for every prescribed rate `K`, uniformly when endpoint distance is at most
`B R` and triangle excess is bounded. This is weaker than the sharp lower
comparison with `exp(-d)`; the subsequent shrinking-ball argument now yields
uniform Ancona comparison along constructed geodesic segments.

A further checked step gives a global polynomial Green product comparison:
for bounded triangle excess at `u i`,
`G(x,y) ≤ H (1+d(xi,yi))^p G(x,u) G(u,y)`, with `H>0`, `p≥0`, and no
endpoint-distance restriction. The ball radius is chosen logarithmically in
endpoint distance, so the avoided mass is absorbed using the coarse lower
bound while the entrance cost is polynomial. The subsequent shrinking-ball
construction removes this factor when the middle orbit point is within a fixed
distance of the constructed geodesic segment.

The finite first/last-entry iteration needed for uniform comparison is now
checked for the actual kernels, without symmetry of the law. Relative losses
accumulate by their sum, and a total loss at most `1/2` gives a factor-two
comparison once terminal endpoint pairs are near the center. The forward and
reflected detour estimates provide the local errors; a checked radius schedule
makes them summable. The required ball sequence is now constructed by halving
the longer side of an axis interval and approximating cut centers by orbit points.
This proves a uniform two-sided Ancona inequality along a constructed geodesic
segment for every pair of orbit endpoints. The bounded-triangle-excess version
is now also proved. Martin limits along different finite boundary rays are
distinct: they grow along their own ray and vanish along every different ray.
Off-diagonal Naïm quotients have positive finite subsequential limits in general.
The new strip argument proves full convergence and joint continuity for opposite
finite endpoints without strong Ancona. Global Naïm chart extension remains
unproved. The analytic ingredients for the contraction step are now
checked: absolutely convergent entrance representations on infinite boundaries,
relative Green entrance identities inside killed domains, and common subtraction
using normalized killed Green columns. The needed uniform comparisons inside
nested geometric domains are still explicit, unproved inputs.

## What Lean checks

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `Singularity/Markov.lean` | Defines right translations and the finite-support right Markov operator on counting-measure `L²(Γ)`; proves its pointwise formula, contraction, and norm bound `≤ 1`. | The nonamenability spectral-gap criterion is proved in `InvariantMean.lean`. The infinite path process is constructed in the later probability modules. |
| `Singularity/Operators.lean` | Proves the Green coercivity identity over real or complex Hilbert spaces; coercivity implies bounded invertibility; compression and adjoint preserve coercivity; strongly convergent vectors permit passage to the limit in a bounded-operator pairing. | The right-inverse equation, contraction, isometric inclusion, and strong convergence are hypotheses of the relevant lemmas. |
| `Singularity/MarkovAdjoint.lean` | Proves composition and inverse formulas for right translations, identifies their adjoints, and proves `P* = P_checkμ`, including the a.e. pointwise formula. | Does not require symmetry or a spectral gap. |
| `Singularity/Green.lean` | From an operator spectral radius `< 1`, constructs `(I-P)⁻¹`; for a contraction proves `1/2`-coercivity and gives the compressed inverse norm bound `≤ 2`. | The spectral gap is assumed. The path-counting identification is proved in `WalkKernel.lean`. |
| `Singularity/GreenSeries.lean` | Derives an eventual geometric norm bound from the spectral radius, identifies the Green resolvent with the norm-convergent series of operator powers, and proves absolute convergence of matrix coefficients. | The operator spectral gap is still assumed; the coefficient identification is proved in `WalkKernel.lean` and `FiniteWalkLaw.lean`. |
| `Singularity/BlockIdentity.lean` | Proves the bounded-operator Schur-complement identity `W − Z M Y = V`. | This abstract lemma takes block equations as hypotheses. The concrete path separator formula is now proved independently in `GreenSeparator.lean` by Dirichlet uniqueness. |
| `Singularity/FourierReduction.lean` | Proves a nonzero kernel for any `N × (N+1)` linear map; positivity of the proposed Liouville multiplier; injectivity of an actual `L²(ℝ)` operator from a nonzero Fourier-multiplier identity; the final factorization contradiction. | The concrete Fourier integral and lattice-translate theorems are proved in the later modules. The geometric current factorization remains unproved. |

The analytic continuation adds the following checked modules:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `DominatedLimit.lean` | Pointwise convergence under a square-summable envelope implies strong `ℓ²` convergence; constructs the limit in `ℓ²` and passes bounded-operator pairings to the limit. | The later GreenPoissonBounds module derives these bounds from the initial distance comparison and bounded-distance ray approaches. |
| `WeightedCauchySchwarz.lean` | Proves the complex-valued weighted integral inequality and its mass-at-most-one version. | The weight's nonnegativity and integrability are explicit hypotheses. |
| `AnalysisOperator.lean` | Constructs the continuous linear map `L² → ℓ²` from row densities, proves its integral coordinate formula and a quantitative norm bound. | Requires nonnegative integrable rows of mass at most one and a uniform finite-column-sum bound. |
| `ExponentialLattice.lean` | Proves summability of the exponential lattice envelope and its square, and a bound uniform in the translation parameter. | Assumes positive lattice spacing. |
| `TranslatedAnalysis.lean` | Derives the column-sum bound from exponential decay of finitely many base profiles; constructs the actual lattice analysis operator. | Still needs the geometric hitting densities to satisfy the base-profile hypotheses. |
| `KernelProjection.lean` | Constructs measurable kernel projections by a proved contraction estimate and Mathlib's mean ergodic theorem. | Uses Cesàro averages instead of the resolvent regularization from the writeup. |
| `MeasurableKernel.lean` | Constructs a measurable unit vector in every nonzero kernel, including families with changing kernel dimension. | The general theorem assumes a measurable operator family; finite-dimensional rank-nullity supplies nontriviality. |
| `FrequencyKernel.lean` | Builds the actual `N × (N+1)` matrix of Fourier samples and proves existence of its measurable unit kernel vector. | This is the input to the now completed finite-band construction below. |

The finite-lattice obstruction is now fully checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `FiniteBand.lean` | Packs a measurable unit vector field into adjacent scalar frequency bands; proves measurability, L² membership, and the exact norm identity `‖φ̂‖² = q`. | Positive band width gives a nonzero L² class. |
| `BandOrthogonality.lean` | Proves the integrated change-of-variables identity and zero pairing against bounded periodic modulations of the frequency profiles. | Integrability is derived from L² membership. |
| `FourierTranslation.lean` | Defines translation and phase multiplication on L², proves Fourier covariance by Schwartz density, and checks lattice phase cancellation. | Uses Mathlib's Fourier convention throughout. |
| `LatticeObstruction.lean` | For every finite family in L²(ℝ) and positive lattice spacing, constructs a nonzero vector orthogonal to all lattice translates; proves their closed span is proper. | No missing measurable-selection, band, or covariance hypotheses. |
| `AnalysisKernel.lean` | Proves the actual bounded lattice analysis operator has a nonzero kernel, and therefore cannot occur in a factorization of an injective operator. | The geometric densities and current factorization still need to be established; Liouville injectivity is proved below. |

The Liouville Fourier calculation and convolution injectivity are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `GammaDensity.lean` | Proves integrability and mass one for `g(t) = exp(t) exp(-exp(t))`; evaluates its Fourier integral as `Gamma(1 - 2πiξ)` and proves nonvanishing. | Uses Mathlib's proved Gamma-function results. |
| `LiouvilleFourier.lean` | Identifies the Liouville kernel with the autocorrelation of g and with `1/(4 cosh²(t/2))`; computes its Fourier transform as a Gamma product, a positive squared norm, and the explicit hyperbolic-sine expression. | Includes the frequency-zero case. |
| `L2Convolution.lean` | Constructs convolution by any L¹ kernel as a Bochner integral of L² translations; proves its norm bound and weak integral formula. | The L¹ condition is explicit. |
| `ConvolutionMultiplier.lean` | Proves the convolution multiplier theorem on all of L², with the required Fubini bound, and obtains injectivity from a.e. nonvanishing. | No assumed Fourier diagonalization remains. |
| `ConvolutionKernel.lean` | Identifies the Bochner operator with its physical-space double-integral pairing; proves absolute integrability using Cauchy–Schwarz. | Handles arbitrary L² inputs and test vectors. |
| `LiouvilleOperator.lean` | Constructs the actual Liouville convolution, proves injectivity, its explicit multiplier and cosh-kernel pairing, then proves the contradiction with factorization through the actual lattice analysis operator. | The base-density hypotheses and geometric current factorization still need to be supplied. |

The passage from scalar kernels to bounded operators is now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `DensityVector.lean` | Constructs the actual ℓ² column vector; proves its uniform norm bound, strong measurability, and the Bochner-integral formula for analysis on L¹∩L². | The density family has a countable index set. |
| `KernelFactorization.lean` | Proves absolute integrability of the paired density kernel, identifies the adjoint composition on L¹∩L², extends by Schwartz density, and derives the analytic contradiction from an a.e. scalar Liouville-kernel identity. | The geometric scalar kernel identity and the base-density conditions are still hypotheses; they are not proved from a random walk. |

The finite-walk and path-kernel connection is now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `CountingL2.lean` | Constructs unit point masses and bounded point evaluation on counting-measure L²; proves evaluation equals pairing with a point mass. | Requires measurable singletons. |
| `WalkKernel.lean` | Defines ordered finite jump paths, their weights, and endpoint sums. Proves normalization, identifies transition weights with coefficients of Pⁿ, and identifies their convergent time sum with the Green resolvent. Also proves left invariance, an entry bound, the diagonal lower bound, and the first-step Green equation. | The spectral gap is still assumed. |
| `FiniteWalkLaw.lean` | Constructs actual PMFs for finite jump paths and their endpoints; proves the endpoint probabilities equal the transition weights and the Green series sums these probabilities. | The infinite law is now constructed in `InfiniteWalkLaw.lean`; geometric convergence and the hitting law are now constructed under the spectral gap in `FuchsianWalkConvergence.lean`. |
| `FirstEntrance.lean` | Defines first entrance through finite path restrictions. Proves nonnegativity, convergence, entrywise F≤G, the time-zero boundary condition, and P-harmonicity outside A. | The operator realization and renewal identities are proved below; `InfiniteFirstEntrance.lean` now identifies these sums with actual first-entrance probabilities. |

The concrete renewal and separator identities are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `SupportedL2.lean` | Models ℓ²(A) as the closed Hilbert subspace of functions supported on A; constructs its isometric inclusion, identifies adjoint restriction pointwise, and gives the coordinate formula for compression. | The coordinate equivalence is proved in `SupportedCoordinates.lean`; the actual normalized strip and finite decomposition are now constructed in `GeometricStrip.lean`. |
| `HarmonicUniqueness.lean` | Proves uniqueness of ℓ² Dirichlet solutions for a contraction with operator spectral radius <1, including inhomogeneous exterior equations. | No symmetry or separate spectral gap for a killed operator is assumed. |
| `FirstEntranceColumn.lean` | Constructs actual ℓ² first-entrance columns by domination by Green columns; proves their boundary values and exterior harmonicity. | Uses countability of Γ and the spectral-gap hypothesis. |
| `EntranceOperator.lean` | Instantiates the compressed Green inverse on the supported space, proves its norm bound ≤2, constructs bounded F, identifies its columns with the first-entrance path sums, and proves G i = F G_A. | Requires a nonnegative normalized finite jump law and the operator spectral gap. |
| `FirstReturn.lean` | Defines convergent first-positive-return path sums, identifies their bounded operator R_A, and proves G_A⁻¹ = I−R_A and its matrix coefficient formula. | The infinite-path stopping-time interpretation and row subprobability estimates are not claimed. |
| `KilledWalk.lean` | Defines and bounds paths avoiding A, constructs their ℓ² Green columns, and proves the exterior Green equation. | All positions, including both endpoints, must avoid A. |
| `GreenSeparator.lean` | Identifies the killed Green operator with G−F i* G; proves the full entrance decomposition and the separator identity, both as operator evaluation and as an ℓ² pairing. | The generic theorem assumes separation. `StripSeparation.lean` now establishes it for the actual bounded-jump strip, and `GeometricGreen.lean` applies this factorization. |

The normalized Green boundary-pairing step is now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `GreenAdjoint.lean` | Proves equality of the operator spectral radii of P and P*, the adjoint resolvent identity, the reflected-law Green operator identity, and G_checkμ(x,y)=G_μ(y,x). | The original spectral gap is assumed; no symmetry is needed. |
| `CountingSequence.lean` | Constructs the isometric coordinate map from counting-measure L² to sequence ℓ²; proves dominated coordinate convergence and constructs supported limits in the actual space used by the separator formula. | The square-summable envelope and coordinate limits are hypotheses. |
| `GreenBoundary.lean` | Defines actual Green rows and columns, proves their coordinate formulas and norm bounds, normalizes the separator pairing, and derives its scalar boundary limit from dominated coordinate convergence. | The normalized geometric separator is now constructed. Green envelopes now follow from the distance comparison and ray approaches; geometric coordinate limits remain unproved. |

The orbit-coordinate and Poisson-envelope connections are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `SupportedCoordinates.lean` | Constructs a linear isometric equivalence between the supported Hilbert space and sequence ℓ² for any enumeration of A; proves surjectivity by extension by zero, preservation of operator norms and pairings, and dominated convergence in these coordinates. | Requires an enumeration of A, supplied algebraically for cyclic orbits below. |
| `CyclicOrbits.lean` | Constructs the enumeration `(n,j) ↦ a^n b_j` from infinite order and distinct cyclic-orbit representatives; proves covariance under integer shifts. | The actual finite strip decomposition is now proved in `StripOrbits.lean` and `GeometricStrip.lean`. |
| `OrbitGreenBoundary.lean` | Transports the actual compressed inverse to ℓ²(ℤ×J), retains the norm bound ≤2, and proves the normalized scalar Green boundary limit from finite-family exponential bounds and pointwise Green-quotient limits. | Requires path separation and the geometric bounds and coordinate limits. |
| `PoissonDecay.lean` | Defines the upper-half-plane Poisson formula, proves an explicit exponential bound for its logarithmic profiles on both boundary sides, proves integrability, and transfers these conclusions to dominated nonnegative densities. | Does not identify random-walk hitting densities or establish their Poisson domination. |
| `PoissonAnalysis.lean` | Constructs the bounded lattice analysis operator and proves its nonzero kernel for measurable nonnegative profiles dominated by constant multiples of logarithmic Poisson profiles. | Poisson domination, positive lattice spacing, and the mass bound ≤1 remain hypotheses. |

The positivity, Harnack, and Martin compactness steps are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `GreenPositive.lean` | Constructs finite paths from submonoid generation, proves positive transition probabilities and strict positivity of all convergent Green entries, and justifies nonzero canonical denominators. | Requires strictly positive weights on the listed support, semigroup generation, and the operator spectral gap. |
| `GreenHarnack.lean` | Proves the fixed-jump and fixed-path Green inequalities; derives Harnack comparison constants independent of the target state. | The spectral gap and positive semigroup-generating support remain hypotheses. |
| `ReflectedSupport.lean` | Proves reflection preserves positivity, total mass, and semigroup generation; derives countability from finite generation. | Does not weaken semigroup generation to group generation. |
| `MartinCompactness.lean` | Defines finite Martin quotients, proves positive lower and finite upper coordinate bounds, extracts pointwise convergent subsequences, and proves positivity, normalization, and harmonicity of limits whose poles escape. | Does not identify the geometric Martin boundary or prove uniqueness of limits. |
| `ReflectedMartin.lean` | Identifies row quotients with reflected Martin quotients, proves reflected harmonicity, and extracts a common subsequence for forward and reflected quotients. | The result is subsequential compactness, not convergence at a specified geometric boundary point. |
| `NaimSubsequence.lean` | Uses the canonical normalizers G(x,o)G(o,y), proves their positivity, and combines Martin compactness with exponential orbit bounds to obtain a subsequential limit represented by the actual compressed-inverse pairing. | Separation and exponential orbit bounds are still geometric hypotheses. The full off-diagonal Naïm limit is not proved. |

The abstract Martin boundary and its group action are now constructed:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `MartinBoundary.lean` | Constructs the closure of normalized Green columns, proves the finite-state map injective and the closure compact, characterizes its boundary as precisely the harmonic functions in the closure, and constructs continuous positive normalized harmonic boundary kernels. | This module constructs the abstract boundary; the later compact Martin modules prove its geometric identification in the cocompact case with infinite orbit of infinity. |
| `MartinApproximation.lean` | Proves finite states are isolated, every boundary point has an escaping finite-pole approximation, escaping pointwise limits lie in the boundary, and the boundary is nonempty for infinite groups. | Requires the same positive semigroup-generating law and spectral-gap hypotheses where indicated. |
| `MartinAction.lean` | Extends left translation to a group action by boundary homeomorphisms; proves the kernel transformation formula and positivity, continuity, and the multiplicative law of its normalization cocycle. | Does not identify the cocycle as a Radon–Nikodym derivative of a hitting measure. |
| `NaimCovariance.lean` | Proves the exact transformation of the finite normalized Green quotient and passes it to any existing limit with forward/reflected Martin-boundary coordinates. | Existence and uniqueness of a full geometric Naïm limit remain unproved. Conditional invariant-current construction is proved below. |

The measure-theoretic current implications are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `WeightedCurrent.lean` | Proves change of variables for weighted measures under measurable equivalences; combines two pushforward densities with kernel covariance to prove weighted-product invariance. Includes almost-everywhere covariance and positive real division factors. | Requires the derivative formulas and covariance. Does not require finite total current mass. |
| `MartinCurrent.lean` | Makes the constructed forward/reflected boundary actions measurable, proves the reciprocal cocycle identity, and applies weighted-product invariance to these actual Martin boundaries. | This module requires measures and derivative formulas on its abstract boundary, plus a measurable full Naïm kernel and covariance. The geometric hitting laws and their Martin derivative formulas are now proved below. No Radon-current or geometric-boundary claim is made. |
| `ErgodicCurrent.lean` | Proves that invariant measurable functions for an ergodic group action are a.e. constant; derives uniqueness up to a scalar for absolutely continuous invariant sigma-finite measures. The scalar is positive and finite when both measures are nonzero. | Group ergodicity and absolute continuity are explicit hypotheses. Cocompact Liouville ergodicity is now proved below. The initial hitting-law rigidity remains unproved. |

The current comparison is now linked to the logarithmic Fourier kernel:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `CurrentComparison.lean` | Positive weights preserve measure classes and nonzero mass; equivalent boundary measures give equivalent weighted-product currents. Equality up to a scalar gives the a.e. real density identity, and boundary densities multiply into the product-current density. | Positivity, measurability, and marginal absolute continuity are explicit. Actual hitting measures are now constructed. Their rigidity properties and the Naïm kernel remain missing; geometric pair-space comparison is proved below. |
| `LogBoundaryMeasure.lean` | Proves the exponential and negative-exponential Jacobian identities as measure equalities, constructs the boundary-pair chart, proves its measurable embedding and null-set pullback properties, and identifies its Liouville density with the previously computed cosh kernel. Derives the full logarithmic scalar identity from a weighted-product current comparison. | Works on the real negative/positive half-lines. It does not identify an abstract Martin boundary with the geometric boundary or prove the geometric current comparison. |
| `CurrentFactorization.lean` | Derives the bounded Liouville operator factorization and analytic contradiction from a measure-level current identity and the logarithmic boundary pairing. | The actual geometric current equality, boundary pairing representation, and lattice-density hypotheses remain inputs. |

The logarithmic analysis operators are now constructed from boundary measures:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `LogBoundaryDensity.lean` | Defines both signed logarithmic densities; proves their pullback-measure formulas, integrability and mass ≤1 from a boundary subprobability measure, actual dilation pushforward densities, translation covariance, and independence of density representatives. Transfers real-boundary Poisson bounds to logarithmic bounds. | Requires a real-chart boundary measure/density. The normalized diagonal matrix-orbit identification is now proved in `DilationOrbit.lean` and `MobiusOrbitDensity.lean`. |
| `BoundaryDensityAnalysis.lean` | Constructs the bounded lattice analysis operator and its nonzero kernel from real-boundary densities, deriving the logarithmic integrability, row mass, and decay conditions. Identifies coordinates using any density representatives of the orbit measures. | Requires positive lattice spacing, boundary mass bounds, Poisson domination, and the dilation pushforward relation. |
| `BoundaryMeasureAnalysis.lean` | Chooses measurable pointwise bounded representatives from real Radon–Nikodym densities with a.e. Poisson bounds, proves they represent the original measures, and constructs the analysis operator directly from those measures. | The actual hitting measures, their absolute continuity and a.e. Poisson bounds still need to be established. |
| `BoundaryMeasureContradiction.lean` | Combines the measure-based analysis construction with the current-to-Fourier contradiction. | The geometric current comparison and strip-pairing representation remain explicit inputs. It is not the singularity theorem. |

The geometric Poisson-measure transport is now verified:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `PoissonMeasure.lean` | Identifies the Poisson kernel with the normalized Cauchy density, proves integrability, total mass one and equivalence with Lebesgue measure, and proves translation and positive-dilation covariance. Defines the measure at an actual Mathlib upper-half-plane point. | Does not identify any random-walk hitting measure with this measure. |
| `PoissonInversion.lean` | Proves the inversion Jacobian and Poisson pushforward covariance, removing the exceptional point using its zero Lebesgue measure. | Uses the finite real boundary chart; the value assigned at the pole has no effect on these absolutely continuous measures. |
| `PoissonMobius.lean` | Proves covariance under every actual `SL(2, ℝ)` transformation, using affine/inversion decomposition and explicit null-set treatment of the boundary pole. | The compact projective boundary and its cocompact Martin identification are proved in later modules. |
| `PoissonDomination.lean` | Transports `ν ≤ B m_z` to `g_*ν ≤ B m_(g·z)` and derives absolute continuity and the required real Radon–Nikodym Poisson bound. | The initial bound for the hitting measure still requires the geometric rigidity theorem. |
| `MobiusBoundaryAnalysis.lean` | Constructs the bounded lattice analysis and its nonzero kernel from finitely many actual Möbius pushforwards of a single bounded boundary probability measure. | Requires the initial measure bound and positive lattice spacing. The normalized periodic strip is now constructed; identification with geometric boundary limits remains unresolved. |

The normalized cyclic action and its orbit densities are now verified:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `MobiusMeasureAction.lean` | Proves the a.e. Möbius composition law, preservation of absolute continuity, and exact pushforward composition and inverse identities for absolutely continuous measures. | The finite-chart maps are not asserted to form a pointwise action at poles. |
| `DilationOrbit.lean` | Constructs the diagonal one-parameter subgroup, proves its integer-power formula and infinite order for nonzero parameters, and identifies the actual `(a^n b)_*ν` measure with dilation of `b_*ν`. | Uses a normalized diagonal element; conjugating a general hyperbolic element remains. The strip is now constructed in `GeometricStrip.lean`. |
| `DilationGeometry.lean` | Identifies the upper-half-plane action with positive scaling, proves axis displacement `|t|`, invariance of the horizontal-to-height ratio, and existence of a cyclic representative with height in `[1, exp(τ))`. | The later strip modules use this normalization to prove separation and a finite cyclic quotient. |
| `MobiusOrbitDensity.lean` | Identifies lattice rows with arbitrary nonnegative measurable densities of the actual matrix orbit measures, simultaneously a.e.; identifies their ℓ² columns and analysis coordinates. | Requires the initial Poisson bound and a normalized diagonal cyclic element. |
| `CanonicalOrbitDensity.lean` | Constructs canonical densities for every Möbius pushforward; proves the simultaneous orbit-column identity and existence of a nonzero L² function annihilating every logarithmic orbit density. | The initial Poisson bound is a hypothesis; actual hitting measures and the geometric current pairing remain unconstructed. |

The actual periodic separator is now constructed in normalized coordinates:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `PeriodicStrip.lean` | Defines the dilation-invariant ratio strip; proves bounded width, compact height normalization, uniqueness in the half-open band, and finiteness of the group representatives using proper discontinuity. | Assumes a discrete subgroup; does not assume a free action or discard stabilizer multiplicities. |
| `StripOrbits.lean` | Constructs the cyclic coordinate bijection for actual strip vertices and proves their finite disjoint orbit decomposition. | Requires a subgroup element equal to the normalized diagonal matrix with positive parameter. |
| `StripSeparation.lean` | Uses the actual hyperbolic metric to rule out bounded jumps between opposite exterior sides, then proves the finite-path separator predicate. | The finite jump-length bound is explicit; `GeometricStrip.lean` supplies it. |
| `GeometricStrip.lean` | Constructs a separator from any finite jump set; proves it contains the identity at base point i and is a finite nonempty disjoint union of cyclic orbits. | Existence and diagonal normalization of a hyperbolic element in a general Fuchsian group remain. |
| `GeometricGreen.lean` | Applies the Green pairing to this concrete strip and its actual cyclic coordinates. | The spectral gap is still assumed. The later modules derive Green envelopes from the distance comparison and ray approaches; geometric boundary limits remain unproved. |

The geometric source of the summable Green bounds is now verified:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `VisualPoissonRay.lean` | Defines the visual Poisson kernel through an actual SL(2,ℝ) height ratio and proves its explicit density formula. Constructs rays from i, proves their radial distance, the uniform Poisson bound, and its `exp(2D)` extension near a ray. | Does not construct group-orbit approximations from cocompactness or identify the full geometric boundary. |
| `VisualPoissonDecay.lean` | Gives an explicit exponential envelope for visual Poisson kernels along integer dilation orbits and proves square summability over every finite family. | The fixed finite boundary coordinate must be nonzero; 0 and infinity are the axis endpoints. |
| `GreenPoissonBounds.lean` | Derives positive denominators, uniform row/column Poisson bounds, and actual cyclic Green quotient envelopes from a two-sided Green-versus-distance comparison. | The initial distance comparison remains a rigidity hypothesis, and bounded-distance ray approaches are supplied as inputs. |
| `GeometricBoundaryLimit.lean` | Derives strong ℓ² convergence and the normalized Green pairing limit on the actual finite periodic strip, supplying both separation and summable domination. | Still assumes the spectral gap, initial distance comparison, ray approximations, eventual opposite sides, and pointwise coordinate limits. |

The cocompact ray construction and its boundary convergence are now verified:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `BoundaryRayApproach.lean` | Proves an explicit Euclidean distance bound to the endpoint for bounded-distance ray approaches; derives boundary convergence, eventual sign, eventual strip avoidance, and hyperbolic escape. | Works at finite real boundary coordinates; the full compact boundary and Martin identification remain separate. |
| `CocompactRayApproximation.lean` | Derives a compact covering set from compactness of the actual orbit quotient, proves a uniform orbit-distance bound, and constructs group sequences with the above convergence and escape properties. | Compactness of the quotient is the cocompactness assumption; no additional ray-approximation hypothesis is imposed. |
| `CocompactBoundaryLimit.lean` | Applies the constructed sequences to the strong ℓ² and Green pairing limit; combines Martin compactness with the actual geometry to extract a Naïm-quotient subsequence without assuming pointwise coordinates. | The spectral gap, initial Green-distance comparison, and normalized diagonal element remain inputs. Full limit uniqueness and identification with the hitting-measure current remain unproved. |

The infinite random walk and its occupation and entrance laws are now constructed:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `InfiniteWalkLaw.lean` | Constructs the product probability measure on jump sequences; proves independence, shift invariance, and that every finite prefix has exactly the existing finite-word law. | Does not assert geometric boundary convergence. |
| `InfiniteWalkProcess.lean` | Defines measurable positions, their recursion and endpoint distributions; identifies the Green kernel as expected total visits and proves almost-sure transience and finite-set escape. | The transience statements assume the operator spectral gap; common escape from all finite sets uses countability. |
| `InfiniteFirstEntrance.lean` | Identifies finite first-entrance events with path weights and F(x,a) with their disjoint union probability. Proves that the row sum of F is the probability of hitting A and is at most one. | A general stopping-time filtration, the strong Markov theorem, and the positive-return interpretation are not asserted. |

The boundary-law construction adds the following modules:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `WalkHeadTail.lean` | Proves independence of the first jump and the entire future, the joint product law, and the first-step integration formula. | Uses the constructed infinite path measure. |
| `WalkBoundaryLimit.lean` | Proves the deterministic-time path cocycle and the almost-sure first-step relation for limits in a Hausdorff equivariant space. | Existence of almost-sure convergence remains an input. |
| `WalkBoundaryLaw.lean` | Defines path-map distributions, proves the finite mixture law, and derives stationarity from a measurable equivariant path limit. | Does not assert that the geometric boundary limit exists. |
| `StationaryQuasiInvariant.lean` | Proves absolute continuity for positive support elements and equivalence of every group translate under semigroup generation. | Applies to a stationary measure; group generation alone is not substituted. |
| `WalkLimitConstruction.lean` | From existence of almost-sure path limits, constructs a measurable version and its stationary probability law, proves uniqueness and quasi-invariance. | Assumes convergence in a metrizable Borel space with continuous equivariant action. The concrete compactification is constructed in the subsequent modules; the full convergence theorem under the spectral gap is supplied in `FuchsianWalkConvergence.lean`. |
| `StationaryDensity.lean` | Defines actual Radon–Nikodym derivatives of translates; proves reconstruction, positivity, normalization, harmonicity, and the derivative cocycle. Real derivatives give positive normalized harmonic functions on one common full-measure set. | The later `HittingMartinDensity.lean` proves this identification for the actual cocompact hitting measure. |

The compact geometric boundary adds the following modules:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `ProjectiveInversion.lean` | Constructs inversion on the one-point compactification of a proper normed field, exchanging zero and infinity; proves involutivity and continuity. | Applies to both ℝ and ℂ. |
| `ProjectiveMobius.lean` | Factors the genuine projective GL(2) action into affine maps and inversion, and proves every transformation is a homeomorphism. | Includes all poles and infinity, without exceptional-point conventions. |
| `CompactBoundary.lean` | Constructs the Borel, metrizable compact real and complex projective lines, the continuous SL(2,ℝ) and subgroup actions, and equivariant upper-half-plane and real-boundary inclusions. Identifies the compact invariant geometric boundary. | Does not assert random-walk convergence. |
| `CompactBoundaryEscape.lean` | Proves every limit of a finite-set-escaping discrete orbit belongs to the geometric boundary. Compactness gives a boundary subsequence; the spectral gap applies this to almost every random path. | Subsequence convergence is not full convergence or uniqueness of the limiting point. |
| `CompactPoissonMeasure.lean` | Lifts the visual measures to the full real boundary and proves probability normalization, zero mass at infinity, and exact group covariance. | The finite-chart comparison uses absolute continuity with Lebesgue measure. |
| `CompactWalkLimit.lean` | Instantiates the previous path-limit construction on the actual sphere, obtaining a stationary probability law of mass one on the geometric boundary and equivalence of its translates. | Still assumes almost-sure convergence and the spectral gap; it does not claim the singularity theorem. |

The convergence and occupation argument adds the following modules:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `CayleyMetric.lean` | Proves the exact disk-coordinate distance formula and the estimate `dist(Cz,Cw) ≤ 4 exp(L) exp(-dist(z,i))` for jumps of length at most L. | Uses the actual hyperbolic metric. |
| `CayleyCompactification.lean` | Identifies the Cayley map with a projective homeomorphism and transfers disk-coordinate convergence to the compact sphere. | Includes the point at infinity. |
| `GeometricPathConvergence.lean` | Proves full compact convergence from bounded jumps and summable radial decay, with eventual positive linear escape as a sufficient condition. Proves the jump bound for every finite-support sample path. | Does not derive linear escape from the group hypotheses. |
| `WeightedOccupation.lean` | Proves the nonnegative weighted occupation formula, square summability of Green rows, and almost-sure path summability for weights dominated by a Green row. | Assumes the operator spectral gap; the occupation formula also uses countability. |
| `GreenEscapeConvergence.lean` | Derives summable radial decay and full geometric convergence from the Green distance comparison; constructs the stationary, quasi-invariant geometric hitting law without a separate convergence assumption. | The spectral gap and Green comparison remain inputs. This does not prove unconditional convergence or the rigidity comparison. |

Independent geometric convergence is now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `HyperbolicGrid.lean` | Gives a coordinate grid on the radius-R hyperbolic ball, with cell diameter at most two and at most `49 exp(4R)` cells. | The exponential constant is deliberately coarse. |
| `HyperbolicOrbitGrowth.lean` | Proves `card B(R) ≤ 49 card B(2) exp(4R)` for group vertices of every discrete subgroup. The proof counts stabilizer multiplicities. | No cocompactness, spectral, or Green comparison hypothesis. |
| `SpectralEscape.lean` | Bounds transition probabilities by power norms, proves a finite-set union bound, and uses Borel–Cantelli to establish escape from slowly growing finite sets. | Requires the corresponding quantitative power decay and cardinality estimates. |
| `FuchsianWalkConvergence.lean` | Derives almost-sure positive linear hyperbolic escape, summable radial decay, full compact convergence, and the stationary quasi-invariant geometric hitting law. Works for every base point. | Requires discreteness, finite support, and the operator spectral gap. The hitting-law theorem also uses positive semigroup-generating support. No Green comparison or separate convergence assumption. |

The hitting law is now connected to the boundary models used by the analytic argument:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `RealBoundaryTransport.lean` | Constructs a measurable inverse of the real boundary inclusion and transfers supported sphere measures, stationarity, and equivalence of group translates. | Reconstruction uses support on the geometric boundary, already proved for the hitting law. |
| `RealGeometricHittingLaw.lean` | Constructs an actual measurable real-projective limit map and its stationary, quasi-invariant probability law. | Uses the established convergence theorem, with the spectral gap still an input. |
| `FiniteBoundaryChart.lean` | Transfers compact measures to ℝ, proves exact reconstruction when infinity has zero mass, and transports Poisson domination, Möbius pushforwards, stationarity, and the real density bound. | Absolute continuity or bounded Poisson domination is explicitly assumed where needed; neither is a rigidity conclusion here. |
| `BoundaryMeasureClasses.lean` | Proves preservation and reflection of mutual singularity across the boundary models, including equivalence between compact visual singularity and real-chart Lebesgue singularity. | The final equivalence allows arbitrary mass at infinity because the visual reference is atomless. It is an equivalence, not a proof of singularity. |
| `GeometricHittingMeasure.lean` | Defines the named `geometricBoundaryMap` and `geometricHittingMeasure`, proves their limit and probability properties, stationarity, quasi-invariance, uniqueness of the law, and actual Radon–Nikodym harmonicity and cocycle identities. | Identification with Martin kernels is proved in `HittingMartinDensity.lean` below in the cocompact case. The final singularity assertion is still unproved. |

The nonamenability spectral-gap implication is now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `QuadraticSpectralGap.lean` | A strict quadratic-form bound confines the full complex spectrum to a smaller disk, by coercivity and invertibility of normalized resolvents. | An abstract Hilbert-space theorem; no symmetry is assumed. |
| `CountingModulus.lean` | Constructs the pointwise modulus in counting-measure L² and proves domination of the Markov quadratic form by its value on moduli. | Uses countability and nonnegative weights. |
| `MarkovEnergy.lean` | Proves the exact translation-energy identity and derives a spectral gap from a uniform positive energy bound. | No laziness, symmetry, or operator norm gap is assumed. |
| `AlmostInvariantL2.lean` | Failure of the spectral gap gives unit vectors almost invariant under every group element. | Finite positive support of mass one generates the group as a semigroup. Countability is derived. |
| `L2SetMass.lean` | Squared L² masses define finitely additive probabilities; proves their translation formula and uniform continuity estimate. | All subsets of the countable group are measurable. |
| `L2InvariantMean.lean` | Ultrafilter limits of those masses give a right-invariant mean; absence of such a mean implies the spectral gap. | Compactness and limits are proved using Mathlib, without new axioms. |
| `InvariantMean.lean` | Identifies left and right invariant means by inversion and proves `rightMarkov_nonamenable_spectral_gap`. | Nonamenability means absence of a nonnegative normalized finitely additive invariant probability on all subsets. The dynamics modules below derive it from an explicitly conjugated hyperbolic element and infinite endpoint orbits; the general nonelementary case remains unfinished. |
| `NonamenableHittingLaw.lean` | Constructs the actual geometric boundary limit and stationary quasi-invariant hitting law from discreteness and nonamenability. | No separate spectral-gap or Green-distance-comparison assumption remains in this theorem. |

The free-subgroup and boundary-dynamics route to nonamenability is now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `InvariantMeanTransport.lean` | Transfers means through equivariant maps and proves inheritance by subgroups and injective homomorphisms, using explicit coset coordinates. | No finite-index hypothesis is imposed. |
| `FreeGroupNonamenable.lean` | Proves that a free group with at least two generators has no invariant mean, using disjoint first-letter cones; derives nonamenability and the spectral gap from an embedded free group. | The embedding must be supplied, or constructed by the later dynamics modules. |
| `NorthSouthPingPong.lean` | Defines uniform attraction outside neighborhoods of a repelling point; proves that large common powers of two such elements with four distinct endpoints generate a free subgroup. | Uses Mathlib's proved ping-pong lemma and finite Hausdorff separation. |
| `NorthSouthConjugate.lean` | Transports the dynamics by conjugation and constructs free powers of an element and a conjugate when their endpoints are distinct. | Requires the stated uniform dynamics. |
| `DilationNorthSouth.lean` | Proves uniform north--south dynamics of a positive diagonal dilation on the full compact real boundary, including infinity. | The matrix is the explicit `dilationMatrix t`, with `t > 0`. |
| `FiniteOrbitDisplacement.lean` | A finite set of points with infinite orbits can be translated away from any finite set. | Uses Mathlib's proved B. H. Neumann coset-cover theorem and orbit--stabilizer equivalence. |
| `NorthSouthNonamenable.lean` | One north--south element with two distinct endpoints having infinite orbits gives an embedded free group and no invariant mean. | The infinite-orbit hypotheses are explicit. |
| `HyperbolicNonamenable.lean` | Applies the full chain to a subgroup of SL(2,ℝ) containing a conjugate of a positive dilation, yielding the spectral gap and actual hitting law. | The later trace-normalization modules now construct the conjugacy; hyperbolic-element existence and infinite endpoint orbits from general nonelementarity remain. Discreteness is needed for the hitting law, not for the free-subgroup obstruction. |

The hyperbolic normalization and change of coordinates are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `HyperbolicEigenvalues.lean` | Constructs the positive reciprocal roots of X²−TX+1 for T>2, their separation, and the positive logarithmic dilation parameter. | Uses the explicit real square root. |
| `HyperbolicNormalization.lean` | Builds an SL(2,ℝ) eigenvector conjugator when the lower-left entry is nonzero. | The eigenbasis is rescaled to determinant exactly one; its original orientation is unrestricted. |
| `HyperbolicTraceNormalization.lean` | Uses elementary shears to cover every remaining matrix of trace >2, proving positive-dilation conjugacy in SL(2,ℝ). | No diagonalizability hypothesis is assumed. |
| `HyperbolicTraceSquare.lean` | Proves tr(g²)=tr(g)²−2 and normalizes the square whenever |tr(g)|>2. | Handles both signs of hyperbolic trace. |
| `TraceNonamenable.lean` | Derives nonamenability, the original spectral gap, and the actual hitting law from a hyperbolic-trace element and infinite boundary orbits. | The element and infinite-orbit hypotheses still need to follow from general Fuchsian nonelementarity. Conjugacy is no longer an input. |
| `ConjugateSubgroup.lean` | Defines B⁻¹ΓB, its group isomorphism and homeomorphism with Γ, discreteness, conjugacy of its two actions, and preservation of infinite boundary orbits. | Supplies a normalized discrete subgroup containing a positive dilation from a hyperbolic trace. |
| `ConjugateCocompact.lean` | Transports a compact orbit cover and proves compactness of the normalized orbit quotient. | Cocompactness of the original group remains an assumption. |
| `BoundaryConjugacy.lean` | Proves that compact-boundary pushforward under the coordinate change preserves and reflects singularity against visual measure. | Applies to arbitrary boundary measures, including atoms at infinity. The named path and hitting laws are identified in HittingConjugacy and NormalizedHittingLaw. |

Hyperbolic-element existence in the cocompact case and absence of point masses are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `SmallRowHyperbolic.lean` | A sequence of matrices with lower row tending to zero, together with an element moving infinity, forces an element of hyperbolic trace. | An explicit determinant/trace argument; no hyperbolic-element assumption. |
| `CocompactSmallRow.lean` | Derives arbitrarily high orbit points from a compact orbit quotient and constructs a sequence with shrinking lower row using im(g i)=1/(c²+d²). | Does not require discreteness. |
| `CocompactHyperbolic.lean` | Cocompactness and an infinite orbit of infinity give a hyperbolic element and a normalized conjugate subgroup containing a positive dilation. | Discreteness is preserved when assumed. Existence beyond the cocompact case remains unproved here. |
| `CocompactNonamenable.lean` | Derives nonamenability, the right operator spectral gap, and the actual geometric hitting law from cocompactness and infinite boundary orbits. | The dynamical condition is explicitly `∀ p, (orbit Γ p).Infinite`. The hitting law also requires discreteness and a finite positive semigroup-generating jump law. |
| `MaximalAtoms.lean` | Proves finite positive-mass level sets and existence of a maximal atom for any finite measure with measurable singletons. | No countability assumption on the space. |
| `StationaryAtoms.lean` | Propagates maximal atoms through the support semigroup; a finite stationary measure has no point masses when every orbit is infinite. | Requires strictly positive support weights, total mass one, and semigroup generation. |
| `HittingMeasureAtoms.lean` | Applies this to the named geometric hitting law; proves zero mass at infinity, exact real-chart reconstruction, preservation of no point masses in the chart, and zero product mass on the boundary diagonal. | Does not assume absolute continuity or a density bound. |

The actual path and hitting laws now respect base points and coordinate changes:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `HittingBasepoint.lean` | Proves bounded-distance paths have the same compact limit under summable radial decay; identifies the chosen boundary maps almost surely and their laws for all base points; proves the actual limit and law from any starting group vertex. | The named law uses the existing discrete-group, positive semigroup-generating support, and spectral-gap hypotheses. Visual singularity is independent of base point. |
| `WalkTransport.lean` | Constructs the support relabeling and measurable path map; proves transport of the one-step PMF, entire infinite product law, and every path position. | The support equivalence must match jump weights and intertwine a group homomorphism. |
| `WalkIsomorphism.lean` | Derives positivity, total mass, semigroup generation, and nonamenability for the image support under an isomorphism, hence its operator spectral gap. | Nonamenability of the source group is assumed here; the cocompact geometric theorem supplies it. |
| `HittingConjugacy.lean` | Identifies actual boundary maps almost surely under the transported path law, identifies their hitting measures exactly, and proves equivalent visual-singularity statements at independently chosen base points. | The coordinate matrix intertwines the two group actions. This equivalence does not assert singularity. |
| `NormalizedHittingLaw.lean` | Defines the actual hitting law for B⁻¹ΓB with the transported support and weights; proves it is the B⁻¹-pushforward of the original hitting law and preserves the singularity conclusion. | Transformed probability, generation, discreteness, and spectral-gap conditions are all derived. The source nonamenability assumption and routine measurable-group structures are explicit. |

The geometric current construction now uses the actual hitting marginals:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `BoundaryPairs.lean` | Defines ordered distinct compact-boundary pairs and their diagonal group action; constructs the restricted product measure, proves it is a probability for nonatomic probability marginals, and constructs the weighted current. A continuous kernel gives a locally finite regular measure; finite real weights give sigma-finiteness. Positive kernels give nonzero mass and preserve measure classes. Marginal absolute continuity passes to the current. | The kernel is supplied. Its existence, continuity, and positivity as the actual Naïm kernel are not asserted. |
| `StationaryCurrent.lean` | Extends covariance cancellation to almost-everywhere positive real densities; proves reconstruction by real Radon–Nikodym derivatives; derives weighted-product invariance from stationarity and covariance in the actual derivatives. | The kernel covariance is explicit. No pointwise positivity of a selected derivative version is assumed. |
| `BoundaryPairInvariance.lean` | Extends a pair-space kernel by zero on the diagonal, identifies the embedded current with the full weighted product, and proves invariance on distinct pairs from the actual stationary-density covariance. | Requires a measurable kernel and its stated a.e. covariance. Nonatomicity ensures that removing the diagonal loses no product mass. |
| `GeometricKernelCurrent.lean` | Names the actual reflected hitting law and the backward-forward pair law; constructs the geometric kernel current from both actual marginals; proves sigma-finiteness, regularity, local finiteness, nonzero mass, comparison with a reference current, and covariance-implied invariance under the respective hypotheses. | Reflection inherits its spectral gap and law hypotheses. Naïm-kernel existence/regularity/covariance and hitting-measure rigidity remain unproved. Cocompact Liouville ergodicity is now proved below. |

The concrete Liouville reference current and its full Möbius invariance are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `BoundaryCircle.lean` | Defines the compact Cayley circle coordinate, proves continuity, injectivity, unit norm, and the exact finite-chart squared-distance formula. | Infinity is included through the compact Cayley homeomorphism. |
| `LiouvilleBoundaryKernel.lean` | Constructs the positive continuous kernel 4π²/dist(Cξ,Cη)² on distinct endpoints; computes its finite-chart formula and cancellation with the two Poisson densities. | This is the explicit Liouville reference kernel, not the Naïm kernel. |
| `LiouvilleCurrent.lean` | Constructs the concrete compact current, proves local finiteness, regularity, sigma-finiteness and nonzero mass, and proves its exact dx dy/(x−y)² chart-measure identity. Marginal absolute continuity gives comparison with this actual reference. | Group invariance and cocompact Liouville ergodicity are proved in the later modules. |
| `LiouvilleTransformations.lean` | Proves translation, positive-dilation, and inversion invariance of the real current; derives the inverse-square pushforward density of Lebesgue measure and handles the null exceptional axes. | No assumed Liouville invariance. |
| `LiouvilleMobius.lean` | Combines the elementary transformations through the affine/inversion factorization of every real special-linear matrix; handles chart poles using product absolute continuity. | Establishes the full finite-chart Möbius invariance. |
| `LiouvilleInvariance.lean` | Transfers invariance to all distinct compact endpoints and gives the invariant-measure property for SL(2,ℝ) and each subgroup. | Does not assert ergodicity of a lattice action. |
| `GeometricLiouvilleComparison.lean` | Applies the proved sigma-finite ergodic uniqueness theorem to the actual hitting-law current and the concrete Liouville reference, yielding a positive finite scalar. | This general comparison assumes ergodicity, marginal absolute continuity and kernel covariance. The cocompact specialization below discharges ergodicity; rigidity and Naïm-kernel inputs remain. |

The Mautner argument and diagonal ergodicity on finite Haar quotients are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `Mautner.lean` | Proves that contraction of conjugates forces a fixed vector for a continuous isometric action; fixes all integral powers of a fixed group element. | Requires continuity of the orbit map at the identity. |
| `ShearContraction.lean` | Computes conjugation of the actual upper and lower shear matrices and proves convergence to the identity along integral multiples of a positive diagonal time. | Both directions of conjugation are treated explicitly. |
| `MautnerSLTwo.lean` | Proves that a vector fixed by one positive dilation is fixed by all of SL(2,ℝ), using both shear subgroups and transvection generation. | Applies to continuous isometric actions on metric spaces. |
| `MautnerDomainAction.lean` | Transfers the theorem to the opposite action used by precomposition, through the inverse homomorphism. | Handles multiplication order without a commutativity assumption. |
| `MautnerErgodicity.lean` | Applies the theorem to actual Lp precomposition actions and to L² indicators; proves that dilation-invariant measurable sets are group-invariant modulo null sets. Derives diagonal-time ergodicity from full-group ergodicity. | Finite regular invariant measure and continuity are required for the invariant-set conclusion. |
| `QuotientErgodicity.lean` | Identifies quotient null sets through full Haar preimages and proves full-group ergodicity on the quotient using a fundamental domain. | The quotient measure must satisfy the fundamental-domain measure formula. |
| `SLTwoHaar.lean` | Proves local compactness, Polish topology, triviality of commutative characters, and right invariance of regular left Haar measures on SL(2,ℝ). | Uses the proved perfection of SL(2,ℝ), so unimodularity is not assumed. |
| `QuotientDilationErgodicity.lean` | Proves ergodicity of every positive diagonal time on a finite Haar quotient. For discrete subgroups, countability and separation are derived; constructing the measure from a finite Haar fundamental domain supplies all quotient-measure hypotheses. | The finite fundamental domain is now constructed in the cocompact modules below. Transfer of ergodicity to the Liouville current is proved in the final modules below. |

The cocompact Haar quotient and the Liouville measure-class correspondence are now checked:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `MeasurableTransversal.lean` | Constructs a measurable injective selection from a finite family of measurable injective sheets, retaining their full image. | An elementary finite induction removes previously represented fibers. |
| `CompactTransversal.lean` | A surjective local homeomorphism onto a compact space has a measurable transversal contained in a compact set. | Local compactness and Borel structures are explicit. |
| `CompactFundamentalDomain.lean` | For a discrete subgroup with compact group quotient, constructs a relatively compact measurable fundamental domain and proves finite mass for locally finite measures. | Uses the actual covering map and the free right action. |
| `CocompactGroupQuotient.lean` | Proves compactness of SL(2,ℝ)/Γ from compactness of Γ\ℍ using properness of the orbit map and inversion; derives a finite measurable Haar fundamental domain. | No finite-domain existence assumption remains in the cocompact setting. |
| `CocompactHaarMeasure.lean` | Defines the domain and its quotient measure, and proves finiteness, nonzero mass, the fundamental-domain formula, invariance, and ergodicity of every positive diagonal time. | The measure is actually constructed from the original discreteness and surface-cocompactness hypotheses. |
| `HomogeneousMeasureClass.lean` | Proves by transitivity, Haar invariance, and Fubini that a homogeneous orbit pushforward and a nonzero invariant sigma-finite measure have identical null sets; includes the inverse-orbit convention. | Does not require the pushforward to have finite total mass. |
| `BoundaryPairTransitivity.lean` | Gives explicit determinant-one matrices reaching every ordered distinct pair from (∞,0), including both infinite-endpoint cases; derives transitivity. | This is the actual compact boundary-pair action. |
| `BoundaryActionMeasurable.lean` | Proves joint measurability of the full SL(2,ℝ) action, including poles, and of its diagonal action on pairs. | Goes beyond the previously checked measurability for countable subgroups. |
| `LiouvilleHaarMeasureClass.lean` | Defines inverse-frame endpoints, proves their dilation invariance and right-multiplication covariance, and identifies the Haar pushforward measure class with the explicit Liouville current. | The descent and transfer of quotient-flow ergodicity are proved in the final modules below. |

Cocompact Liouville ergodicity is now fully discharged:

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `InvariantSetDescent.lean` | Intersects the inverse translates of an almost-invariant measurable set under a countable group; proves measurability, exact invariance, equality modulo null sets, and descent to a measurable quotient set. | Treats almost-invariance explicitly, without selecting a representative point in each coset. |
| `QuotientFlowDuality.lean` | Transfers ergodicity of a quotient time map to the lattice action through an equivariant endpoint map with the same measure class. | The endpoint map's measurable and equivariance properties, measure-class comparison and quotient ergodicity are explicit inputs here and proved in the concrete application. |
| `CocompactLiouvilleErgodicity.lean` | Proves `ErgodicSMul Γ BoundaryPair compactLiouvilleCurrent` from discreteness and compactness of Γ\ℍ, using the actual Haar quotient, Mautner theorem, endpoint map, and Liouville current. | No ergodicity, fundamental-domain existence, or measure-class identification is assumed. |
| `CocompactCurrentComparison.lean` | Derives current proportionality to the concrete Liouville current without an ergodicity hypothesis in the cocompact case. | Hitting-law absolute continuity and the positive measurable kernel's covariance in actual derivatives remain explicit; these do not yet construct the Naïm kernel. |

All these proofs are checked by Lean. No theorem or definition in the project uses
`sorry`, `admit`, or a new axiom. The axiom audit permits only Lean's usual
`propext`, `Classical.choice`, and `Quot.sound`.

## Toolchain and verification

- Lean: `leanprover/lean4:v4.34.0-rc2`
- Mathlib commit: `3649549a1e4b19461e912299ca7127d8831b79fa`
- The full dependency lock is in `lake-manifest.json`.

In this directory, run:

```sh
python3 verify.py
```

This builds all modules, asks Lean for the axioms of every new theorem and
definition, checks that the audit covers those declarations, and rejects any
axiom outside the allowed set. The report is saved in `VERIFICATION.txt`.

Equivalently, the main compiler commands are:

```sh
lake build
lake env lean Audit.lean
```

On this machine, `.lake/packages` contains links to the already installed
`~/Lean/mymath/.lake/packages` dependencies. The source archive excludes these
links and all build products. On another machine, install the pinned Lean toolchain,
allow Lake to fetch the locked dependencies, and use `lake exe cache get` to obtain
Mathlib's compiled cache before building.

## Conventions that matter

`rightMarkov` acts by `P f(x) = Σ μ(g) f(xg)`, on complex `L²` with counting measure.
The coefficients are real, nonnegative, and sum to one. No symmetry is imposed.

`compression i G` is `i.adjoint ∘ G ∘ i`, for a linear isometric embedding `i` of
Hilbert spaces. It is not a killed Green operator.

`Coercive T c` means `c * ‖v‖² ≤ Re ⟪T v, v⟫` for every `v`. The proofs do not assume
self-adjointness or confuse this condition with preservation of nonnegative functions.

Mathlib's Fourier transform uses `exp(-2π i x ξ)`. The writeup uses angular
frequency `ω`. Thus the multiplier expression in Mathlib's convention is
`c * liouvilleMultiplier (2 * π * ξ)`. The Fourier integral, its value at zero,
positivity, and the multiplier identity on L² are all now checked.

## Reading order

For the operator argument, start with `Operators.lean` and `Green.lean`. For the
Fourier argument, start with `LatticeObstruction.lean`; for its application to the
analysis operator, read `AnalysisKernel.lean`. The combined analytic contradiction
is `impossible_liouville_kernel_identity` in `KernelFactorization.lean`. It assumes
only the scalar kernel identity and base-density conditions, deriving the operator
factorization. These hypotheses still need to be established for the geometric
objects. Read `DEPENDENCIES.md` for the remaining probability and geometry before
interpreting it as a singularity result.

## Measurable-selection proof used in Lean

For an operator `B`, define `T = I − a B*B` with `a = (1 + ‖B‖²)⁻¹`.
Lean verifies that `T` is a contraction and that its fixed vectors are exactly
`ker B`. The mean ergodic theorem gives convergence of the Cesàro averages of
`T` to the kernel projection. Each approximating vector varies continuously with
`B`, so the projection of a fixed vector varies measurably.

A fixed countable dense sequence has some nonzero projection whenever the kernel
is nontrivial. Select the first such vector and normalize it. The selection and
normalization are proved measurable. This replaces the regularized-inverse and
column-norm-threshold construction; those particular formulas are not claimed
verified. The result needed by the Fourier proof is now proved directly for its
frequency matrix.

In Mathlib's Fourier convention, the adjacent frequency spacing corresponding
to translation by `τ` is **`q = 1/τ`**, not `2π/τ`. The latter belongs to the
angular-frequency convention of the writeup.

## Finite-band construction now verified

For the measurable unit kernel vector `v(ω)` and `q > 0`, set
`φ̂(ω + lq) = v_l(ω)` for `0 ≤ ω < q` and `l = 0,…,N`, and set `φ̂ = 0`
outside those bands. The half-open cells are disjoint. Lean proves
`∫ |φ̂|² = ∫_[0,q) ∑_l |v_l|² = q`.

Translation by `n/q` multiplies the Fourier transform by
`exp(-2π i (n/q) ξ)`. That phase is unchanged when `ξ` is shifted by `lq`.
Unfolding the integral over the bands therefore produces the matrix-kernel
identity. The inverse Fourier transform is nonzero and orthogonal to every
translate. This is proved for arbitrary complex L² profiles, not only smooth or
integrable profiles. `translated_analysis_has_kernel` then applies it to the
nonnegative density families used by the proof.

## Liouville convolution now verified

The proof uses the elementary density `g(t) = exp(t) exp(-exp(t))`. Substitution
`x = exp(t)` gives `Fourier(g)(ξ) = Gamma(1 - 2πiξ)`. The same substitution proves
that its autocorrelation is `exp(-t)/(1 + exp(-t))² = 1/(4 cosh²(t/2))`.
The convolution theorem gives the product of the two conjugate Gamma values.
Euler's reflection formula evaluates it as `πω/sinh(πω)` for `ω = 2πξ`, with
value one at zero. All these substitutions and identities are checked in Lean.

For an L¹ kernel k, convolution on L² is defined by the Bochner integral
`C_k f = ∫ k(t) T_t f dt`. Translation continuity and the L¹–L² norm bound are
proved. Fourier covariance and an absolutely integrable scalar double integral
show `Fourier(C_k f) = Fourier(k) Fourier(f)` almost everywhere. A second Fubini
argument identifies the weak physical-space kernel. Thus injectivity is proved
for the actual convolution operator used in the final analytic contradiction.

## Scalar kernels and operator factorization now verified

For a countable density family K with overlap bound B, the vector
`v_K(t) = (k_i(t))_i` has ℓ² norm at most B and is strongly measurable. For
`f ∈ L¹∩L²`, Lean proves `H_K f = ∫ f(t) v_K(t) dt`. Thus the weak kernel of
`H₋* M H₊` is `⟪v₋(s), M v₊(t)⟫`. The paired integrand is absolutely integrable
on this test class, by the product of the two vector L¹ bounds and `‖M‖`.

An a.e. equality of this scalar kernel with `c/(4 cosh²((s-t)/2))` gives equality
of pairings on Schwartz functions. Density and continuity extend this to an
identity of bounded operators on all of L². The existing injectivity and lattice
obstruction then give a contradiction for `c > 0`. Both iterated-a.e. and
product-a.e. forms of the scalar kernel hypothesis are supported. This argument
does not assume absolute convergence of a double matrix sum for arbitrary M.

## Finite paths and first entrance now verified

`WalkWord s n` is an ordered word of n jumps from s. Its weight is the product of
the corresponding real jump weights. Under nonnegativity and total jump mass one,
these weights form a PMF. Pushing it forward by right multiplication of the jumps
gives an actual endpoint PMF, whose values are the transition weights pₙ(x,y).

Lean proves `(Pⁿ δ_y)(x) = pₙ(x,y)` and, under the operator spectral gap,
`(G δ_y)(x) = Σₙ pₙ(x,y)`. Thus the previously abstract resolvent now has its
path-counting interpretation. The nonamenability criterion supplying the gap is
now proved in `InvariantMean.lean`. Boundary convergence under that gap is proved below.

A first-entrance word ending at a∈A has all positions at times 0,...,n−1 outside A.
Summing its weight defines Fₙ(x,a). The inequalities `0≤Fₙ≤pₙ` imply convergence
of F=ΣₙFₙ and `0≤F≤G`. The boundary condition is F(x,a)=1 if x=a∈A and zero
for distinct x,a∈A; outside A, F satisfies `F(x,a)=Σ_g μ(g)F(xg,a)`.
The later `EntranceOperator.lean` now supplies the bounded operator realization,
with norm at most `2‖G‖`, by the Dirichlet uniqueness argument below.

## Renewal and separator identities now verified

The Hilbert space denoted ℓ²(A) is implemented as the closed subspace of
counting-measure L²(Γ) whose elements vanish outside A. Its inclusion i is an
isometry, and Lean proves that i* retains exactly the A-coordinates. Applying the
existing coercivity theorem gives a bounded inverse M_A of `G_A=i*Gi`, with
`‖M_A‖≤2`.

The bounded operator `F=GiM_A` takes its prescribed boundary values and is
P-harmonic outside A. The path-counting first-entrance columns have the same
properties and belong to ℓ² by `0≤F(x,a)≤G(x,a)`. Dirichlet uniqueness identifies
them with the operator columns. This proves boundedness of the probabilistic F
and `Gi=FG_A`, rather than assuming those operator relations.

Taking one jump and then first entering A defines the first-positive-return
series. Its bounded operator is `R_A=i*PF`. Restricting `(I−P)F=iM_A` proves
`M_A=I−R_A`, including the coefficient identity with a nonnegative return kernel.

A parallel construction counts paths that avoid A throughout. Their ℓ² columns
solve the exterior Green equation with zero boundary values, so uniqueness
identifies their operator as `K_A=G−Fi*G`. If A meets every finite jump path from
x to y, its killed coefficient is zero. Lean then proves
`G(x,y)=⟪i*G*δ_x, M_A(i*Gδ_y)⟫`. This is a bounded Hilbert-space pairing; no
absolute convergence of an arbitrary matrix double sum is presumed. The formal
proof uses Dirichlet uniqueness in place of the writeup's block-inverse route.

## Normalized Green boundary pairing now verified

The reflected Green operator is G*, and its kernel is the transpose of the
forward kernel. Thus the actual row on A is `i*G*δ_x`, while the column is
`i*Gδ_y`. Their norms are at most ‖G‖. Real normalizations r and c give
`G(x,y)/(rc) = ⟪row_x/r, M_A(column_y/c)⟫` whenever A separates x and y.

`normalizedGreen_boundary_limit` now passes this identity to the limit for the
actual path Green kernel and compressed inverse. Its hypotheses are eventual
path separation, coordinatewise convergence of each normalized vector, and a
square-summable envelope for each family. The proof constructs both supported
limit vectors, proves norm convergence, and uses continuity of the pairing.
It does not presume absolute convergence of a matrix double sum. Producing these
hypotheses from hyperbolic geometry and identifying the limits with Martin
kernels remain separate obligations.

## Orbit coordinates and Poisson bounds now verified

For an enumeration e of A, `supportedCoordinatesEquiv e` sends f to its values
at e(i). Its inverse extends a sequence by zero outside A. Lean proves the two
maps form a linear isometric equivalence. Conjugating M_A by this equivalence
preserves its operator norm and pairing exactly. For a union of distinct cyclic
orbits of an infinite-order element a, the required enumeration is constructed
as `(n,j) ↦ a^n b_j`.

`orbitGreen_boundary_limit` works directly with scalar Green quotients at those
coordinates. If the quotients converge pointwise and admit bounds
`C_j exp(-τ|n|)` and `D_j exp(-σ|n|)`, where τ,σ>0 and J is finite, it constructs
the sequence-space limits, proves strong convergence, and identifies the scalar
limit with the pairing through the transported M_A. The normalized geometric strip
and separation are now proved. Green bounds follow from the initial distance
comparison and ray approaches in `GreenPoissonBounds.lean`; the initial comparison
and geometric Martin-kernel identification still need proofs.

The elementary Poisson step is also proved. With
`P_(x,y)(u)=y/[π((u−x)²+y²)]` and y>0,
`exp(t) P_(x,y)(exp(t)) ≤ C(x,y) exp(-|t|)`, where
`C(x,y)=(2y²+2x²+1)/(πy)`. The negative-side formula follows by replacing x by −x.
The envelope is integrable. Consequently, measurable nonnegative profiles
bounded by multiples of these Poisson profiles automatically satisfy the
integrability and decay inputs of the analysis construction. The resulting
bounded operator has a proved nonzero kernel; the random-walk comparison that
would give this domination is not assumed established.

## Green positivity and Martin compactness now verified

Strictly positive weights on a semigroup-generating finite support give a
positive-weight finite path from x to y. The convergent Green series therefore
satisfies G(x,y)>0. Thus the normalizers G(x,o) and G(o,y) in the canonical
Green quotient cannot vanish.

For a fixed path w from x to z, Lean proves
`weight(w) G(z,y) ≤ G(x,y)` for every target y. Using paths in both directions
bounds each Martin coordinate `G(z,y)/G(o,y)` above and away from zero, uniformly
in y. The group is countable because it is generated by finite words in the
finite support. Compactness of the product of the coordinate intervals gives a
pointwise convergent subsequence. If the poles escape every fixed state, the
finite-support Green equation passes to the limit and proves that the limit is
a positive harmonic function normalized to one at o.

The reflected walk inherits semigroup generation, positivity, and the spectral
gap. Its quotients are exactly `G(x,z)/G(x,o)`. A common subsequence for the two
families is now constructed. `finiteNaim_pairing_subsequence` combines these
actual coordinate limits with the proved orbit-envelope convergence theorem:
under separation and exponential bounds, the normalized rows and columns
converge strongly and `G(x,y)/(G(x,o)G(o,y))` converges along that subsequence to
their pairing through the actual M_A. No coordinate-limit hypothesis is needed
for this subsequential result. Uniqueness of these limits and identification
with geometric boundary kernels remain unproved.

## The abstract Martin boundary is now constructed

`martinClosure` is the closure of the actual map
`y ↦ (z ↦ G(z,y)/G(o,y))` in the topology of pointwise convergence. The finite
Green equation gives a continuous defect which is nonzero at precisely the
pole. Lean uses this to prove injectivity, isolate finite states, and show that
the complement of the finite states in the closure consists exactly of the
harmonic functions in that closure. Harnack bounds make the closure compact
and every coordinate strictly positive. The boundary itself is closed and
compact, and evaluation supplies continuous positive normalized harmonic kernels.

Every abstract boundary point is the pointwise limit of finite columns whose
poles escape every fixed state. For an infinite group, an injective sequence of
poles and the proved subsequence theorem show that the boundary is nonempty.
This constructs an actual boundary, rather than taking a boundary-kernel family
as an assumption. Its identification with the geometric Fuchsian boundary
remains a separate obligation.

The normalized formula `(g·H)(z)=H(g⁻¹z)/H(g⁻¹o)` extends left translation of
finite poles and defines homeomorphisms of the constructed boundary. Lean
checks the action laws and the positive cocycle `c(g,H)=H(g⁻¹o)`, with
`c(gh,H)=c(g,h·H)c(h,H)`.

Finally, for `Θ(x,y)=G(x,y)/(G(x,o)G(o,y))`, left invariance gives
`Θ(gx,gy)=Θ(x,y)/(K_checkμ(g⁻¹o,x) K_μ(g⁻¹o,y))` at finite poles.
`naim_limit_translate` passes this formula to any existing quotient limit and
its forward/reflected Martin-boundary coordinates. This proves the covariance
calculation, but does not prove existence of the full Naïm limit or identify the
cocycle with a hitting-measure derivative.

The new current construction is conditional on those remaining inputs. With the
convention `c(g,ξ)=K(g⁻¹o,ξ)`, the required measure formula is
`g_*ν = c(g⁻¹,·) ν`. For the product of the two boundary measures, change of
variables gives the transformed density
`c_checkμ(g⁻¹,ξ) c_μ(g⁻¹,η) Θ(g⁻¹ξ,g⁻¹η)`. The kernel covariance makes this
exactly `Θ(ξ,η)`. Lean checks this cancellation on the actual abstract Martin
boundaries and allows infinite total mass.

Separately, the ergodic uniqueness theorem applies to sigma-finite invariant
measures `J ≪ L` for an ergodic group action on `(X,L)`. It proves `J = c L`,
with `0 < c < ∞` when both measures are nonzero. It uses a.e. invariance of the
Radon–Nikodym derivative and group ergodicity, not ergodicity of an individual
group element. Cocompact Liouville ergodicity, sigma-finiteness and nonzero
current mass are now supplied by later modules. Hitting-law absolute continuity
and the actual Naïm-kernel properties remain to be established.

The current-to-kernel change of coordinates is now a measure-level proof.
`logBoundaryPair(s,t)=(-exp(s),exp(t))` pushes the measure with density
`exp(s) exp(t)` to product Lebesgue measure on the opposite half-lines. Weighting
by the classical Liouville density gives exactly the measure with density
`1/(4 cosh²((s-t)/2))` in logarithmic coordinates. The proof uses the derivative
change-of-variables theorem, not an assumed Jacobian identity.

The chart is a measurable embedding and pulls back product-Lebesgue null sets
to null sets. Consequently an equality of currents gives an a.e. equality of
logarithmic densities. `CurrentFactorization.lean` feeds this identity into the
already verified operator and Fourier arguments. The remaining work is to
construct the geometric objects and prove the current comparison and boundary
pairing for them; these are still explicit hypotheses.

For a real boundary density `f`, the definitions now give
`k⁺(t)=exp(t) f(exp(t))` and `k⁻(t)=exp(t) f(-exp(t))`.
Both are integrable with mass at most one when the original measure has mass
at most one. Pushing a boundary measure forward by `u ↦ exp(a) u` gives the
real density `exp(-a) f(exp(-a) u)`; the corresponding logarithmic density is
`k(t-a)`. The a.e. version holds for any nonnegative measurable density
representatives of those same measures.

`BoundaryMeasureAnalysis.lean` starts from the measures themselves and a.e.
Poisson bounds for their real Radon–Nikodym derivatives. Capping by the bound
changes each density only on a null set and provides the pointwise bounds used
by the analysis construction. `impossible_boundaryMeasure_current_identity`
then accepts these boundary measures, a geometric current comparison, and a
strip-pairing representation; it derives the analytic contradiction without
additional assumptions on logarithmic mass, integrability, or exponential decay.

The Poisson measure is now normalized and equivariant under the full real
special linear group acting on Mathlib's upper half-plane. The real-chart
formula `(a u+b)/(c u+d)` is used for the boundary map. For `c≠0`, the proof
removes the exceptional pole `-d/c`, a null set for every Poisson measure.
No pointwise action on the whole real line is asserted at those exceptional
values.

A bound `ν ≤ B m_z` now automatically gives the same bound after each Möbius
pushforward, with the base point changed to `g·z`. The real Radon–Nikodym
bound and the finite-family analysis operator are derived from it. The initial
boundedness of the actual hitting measure under nonsingularity remains a
geometric rigidity obligation; it has not been assumed as a new axiom.

The boundary composition law is now checked almost everywhere and gives an
exact action on absolutely continuous measures. For
`a = diag(exp(τ/2), exp(-τ/2))`, integer powers act as `u ↦ exp(nτ) u`.
Consequently `(a^n b_j)_*ν` has logarithmic density `k_j(t-nτ)` a.e., with a
single full-measure set valid for every `(n,j)`. Canonical Poisson-capped
Radon–Nikodym representatives identify the actual ℓ² columns without additional
choices of orbit densities. `exists_nonzero_orthogonal_mobiusOrbit` supplies a
nonzero L² function annihilating all these actual logarithmic orbit densities.
This conclusion still assumes `ν ≤ B m_z`; it does not prove the initial
boundedness theorem for hitting measures or the geometric current identity.

The periodic separator no longer needs to be assumed for a discrete subgroup
containing `diag(exp(τ/2), exp(-τ/2))`, with `τ > 0`. The formal proof uses
`|re(z)/im(z)| ≤ sinh(L/2)+1`, where `L` is the sum of the finite jump lengths.
This strip has bounded hyperbolic width and prevents jumps from crossing its
two exterior sides. A half-open height band supplies canonical representatives;
proper discontinuity makes their set finite. The resulting decomposition is
nonempty at base point i, disjoint as a decomposition of group vertices, and
feeds directly into the Green pairing. The construction does not assume the
action is free. The general hyperbolic-element normalization, nonamenability of
the relevant Fuchsian groups, initial Green-distance comparison, full Martin-boundary
identification, and current comparison still remain. The generic spectral criterion
and actual geometric hitting-law construction are now proved. Ray approximations and their
eventual sides are now derived from compactness of the orbit quotient.

The geometric domination step is now checked uniformly across the infinite strip.
Sending ξ to infinity reduces the radial estimate to the hyperbolic
logarithmic-height inequality. The resulting visual kernel satisfies an explicit
`C_(ξ,w) exp(-τ|n|)` bound along the dilation orbit for ξ ≠ 0. Given the initial
two-sided Green-distance comparison, this produces both normalized Green
envelopes, including for a nonsymmetric walk. `geometricStrip_boundary_limit`
uses these bounds and the constructed finite separator to prove strong ℓ²
convergence and the scalar pairing limit from pointwise coordinate convergence.
It does not assume a summable envelope or separator predicate. The subsequent
cocompact version now also derives group ray approximations and eventual sides.
The initial comparison and geometric identification of the coordinate limits
still need proofs.

Compactness of the actual orbit quotient now produces the group-ray sequences
used above. The proof constructs a compact covering set through the open
quotient map, obtains a uniform radius, and chooses orbit points near integer
times on each ray. These sequences converge to the prescribed finite boundary
point, eventually have its sign, leave every fixed ratio strip when the endpoint
is nonzero, and escape every fixed group vertex. The cocompact pairing theorem
therefore no longer assumes ray approximations or eventual sides.
`cocompactStrip_naim_subsequence` also derives a convergent subsequence by Martin
compactness. This is a subsequential result, not existence or uniqueness of the
full Naïm kernel; the initial rigidity comparison and spectral gap remain inputs.

The random walk now lives on one infinite probability space of independent
support-valued jumps. Its finite-prefix and time-n endpoint laws agree exactly
with the earlier path weights and transition kernel. The nonnegative occupation
count has expectation G(x,y), and the spectral-gap hypothesis implies almost-sure
escape from every finite set of a countable group. First entrance at a prescribed
vertex is also an actual measurable event: its probability is F(x,a), and summing
over entrance vertices gives the probability of ever hitting A. The following
modules construct the hitting-law machinery, and `FuchsianWalkConvergence.lean`
now supplies full geometric convergence under the spectral gap. The remaining
geometric rigidity results are still unproved.

The first jump is now proved independent of the entire infinite tail. This
identifies the distribution of any measurable function of the head and tail with
its finite mixture of section laws. Almost-sure convergence of orbit positions
in a Hausdorff equivariant space then forces the first-step limit relation.
In a metrizable Borel space the limit has a measurable version; its pushforward
is a stationary probability measure independent of all choices on null sets.
Strictly positive support and semigroup generation make every translate equivalent
to this law. The actual Radon–Nikodym derivatives reconstruct the translated
measures and satisfy both the harmonic equation and the group cocycle identity.
Finite generation supplies countability, so positivity, normalization, and the
harmonic identities hold on one common full-measure set. The abstract construction takes convergence as input; the concrete convergence
theorem now discharges that input under the spectral gap. Identification of
these densities with Martin kernels remains unproved.

The geometric boundary model is now concrete. `OnePoint ℝ` is the compact real
projective line, included equivariantly in the compact sphere `OnePoint ℂ`.
Inversion exchanges zero and infinity continuously; an affine–inversion
factorization proves continuity of every projective Möbius transformation.
The upper-half-plane inclusion is an equivariant open embedding. Proper
discontinuity then rules out interior limits for any orbit path escaping every
finite set. This proves that almost every transient path has a boundary
accumulation subsequence. The compact visual measures have exact covariance.
`exists_compact_geometric_hittingLaw` combines the actual topology and action
with the measurable path-limit construction and proves full mass on the boundary,
stationarity, and quasi-invariance, assuming existence of almost-sure limits.
`FuchsianWalkConvergence.lean` now supplies these limits from discreteness and
the operator spectral gap, independently of the Green comparison.

The Cayley-coordinate estimate now turns summable radial decay into full path
convergence. The weighted occupation identity is proved for arbitrary nonnegative
vertex weights. Since every Green row is square-summable, a weight bounded by
`C G(1,g)` is summable along almost every path. The lower Green comparison bounds
`exp(-dist(g i,i))` by this weight. Thus
`exists_compact_hittingLaw_of_comparison` constructs the actual geometric hitting
law from the comparison and spectral gap, without assuming path convergence.
This is a conditional result: it cannot be used circularly to establish the
comparison from a rigidity theorem that already presupposes the hitting measure.
The independent escape argument is now proved in `HyperbolicOrbitGrowth.lean`,
`SpectralEscape.lean`, and `FuchsianWalkConvergence.lean`. Its remaining input
is nonamenability of the relevant Fuchsian group; the derivation of the spectral
gap from absence of an invariant mean is now complete.

The independent convergence proof uses the bound
`card B(R) ≤ 49 card B(2) exp(4R)`, which is proved directly from a Euclidean
coordinate grid and proper discontinuity. Each grid fiber injects by translation
into the radius-two group ball, so finite stabilizers are fully accounted for.
The operator spectral gap gives an eventual bound `p_n(x,y) ≤ q^n`, with
`0 < q < 1`. Choosing a positive a with `exp(4a) q < 1` makes the probabilities
of `X_n ∈ B(an)` summable. Borel–Cantelli yields positive linear escape.
Bounded hyperbolic jumps and the Cayley estimate then give full convergence.
`exists_geometric_hittingLaw` combines this with the proved stationary-law
construction, without any Green-distance comparison hypothesis. The remaining
Fuchsian nonamenability and rigidity/current identifications are not proved by it.
`NonamenableHittingLaw.lean` now supplies the spectral criterion explicitly.

The hitting measure now has a concrete real-projective definition:
`geometricHittingMeasure` is the pushforward of the infinite walk law by the
constructed measurable boundary limit. Any other version of that limit gives
the same law. Its actual Radon–Nikodym derivatives satisfy positivity,
normalization, harmonicity, and the group cocycle identity. The later
`HittingMartinDensity.lean` now identifies these derivatives with the geometric
Martin kernels under the cocompact hypotheses.

`finiteBoundaryMeasure` connects this measure to the real-chart analytic modules.
Under an initial compact Poisson bound it gives a probability measure with the
required Lebesgue density estimate and exact Möbius transport. The initial bound
remains the missing rigidity input. Independently of that bound, and even if
there is mass at infinity, `geometricHittingMeasure_singularity_iff` proves that
the desired compact-boundary singularity is equivalent to singularity of the
extracted real measure against Lebesgue measure. This supplies the change of
boundary models for the final conclusion, without assuming that conclusion.

The nonamenability criterion applies directly to the original right Markov operator.
If its spectral radius were not below one, the energy criterion would supply unit
vectors with energy tending to zero. Positive support weights and semigroup
generation make them almost invariant under every translation. Their squared
masses on arbitrary subsets have ultrafilter limits in [0,1]. The continuity
estimate for set masses makes the limit a finitely additive invariant probability,
contradicting nonamenability. Inversion passes between the right and left conventions.
This argument does not pass to a lazy walk. The free-subgroup proof is now supplied, and the boundary-dynamics route is
instantiated for an explicitly conjugated positive dilation. Hyperbolic-element existence and the infinite-orbit hypotheses from general
Fuchsian nonelementarity remain to be proved; the diagonal conjugacy is now constructed from |tr(g)| > 2.

The group-theoretic nonamenability route no longer assumes a free subgroup.
`exists_free_subgroup_of_northSouth` constructs it from uniform attraction and
infinite endpoint orbits. B. H. Neumann's lemma supplies a conjugate with disjoint
endpoints; finite Hausdorff separation supplies the ping-pong neighborhoods.
The forward inclusion gives the inverse inclusion by contraposition. Mathlib's
ping-pong theorem then proves injectivity of the actual free-group homomorphism.

For a positive dilation, compact sets in the real chart are bounded and the
complement of a neighborhood of zero is bounded away from zero. The factor
exp(nt) therefore proves the required uniform attraction to infinity.
`fuchsian_no_invariantMean_of_hyperbolic` transports this through an arbitrary
SL(2,ℝ) conjugacy and applies the group-theoretic chain. The resulting
`exists_real_geometric_hittingLaw_of_hyperbolic` assumes neither nonamenability nor
a spectral gap separately. Its explicit geometric inputs still need to be
obtained from the intended general hypotheses.

Hyperbolic diagonalization is now explicit. For trace T>2 the two real roots are
r=(T+sqrt(T²−4))/2 and s=(T−sqrt(T²−4))/2. With lower-left entry c≠0,
the eigenvectors (r−d,c) and (s−d,c) have determinant c(r−s). Rescaling the
first column by its reciprocal gives an SL(2,ℝ) conjugator. If c=0, one of two
fixed lower triangular shears makes it nonzero; otherwise the determinant and
trace conditions contradict each other. For negative hyperbolic trace, the
identity tr(g²)=tr(g)²−2 reduces to this positive-trace case.

The resulting subgroup B⁻¹ΓB is homeomorphic and isomorphic to Γ. The actual
hyperbolic and boundary actions are conjugate. Discreteness, infinite boundary
orbits, and compactness of the orbit quotient are preserved. Visual singularity
is also preserved and reflected by the compact-boundary pushforward. Existence
of the initial hyperbolic-trace element remains to be derived from the general
nonelementary hypotheses. The transformed named random-walk law is now identified
in `NormalizedHittingLaw.lean`.

In the cocompact case, existence of the hyperbolic element is now proved under an
infinite orbit of infinity. Uniform orbit density gives matrices g_n whose images
of i have imaginary parts tending to infinity, so their lower entries c_n,d_n
tend to zero. If all traces had absolute value at most two, the trace identities
for g_n and g_n b, together with det(g_n)=1, would force b's lower-left entry to
vanish. An infinite orbit of infinity supplies a b for which that entry does not
vanish, a contradiction. Combining this with the existing normalization and
free-subgroup construction proves the cocompact spectral gap under the explicit
infinite-boundary-orbit hypothesis. The noncocompact group case and any required
equivalence with other definitions of nonelementarity remain separate obligations.

The actual hitting law is now proved to vanish on all singletons under the same
infinite-orbit hypothesis. If a finite stationary measure had an atom, a maximal
one would exist. The convex stationarity equation forces every positive-jump
predecessor to have the same maximal mass; semigroup generation propagates this
to its entire group orbit. A positive-mass level set is finite, contradicting
infinite orbits. Thus infinity has zero mass and finite-chart reconstruction is
exact without assuming absolute continuity. Boundary products give zero mass to
the diagonal, which justifies passing to pairs of distinct endpoints.

Base-point and conjugacy identification no longer remain assembly assumptions.
Summable radial decay and the Cayley-distance estimate show that two orbit paths
at bounded hyperbolic distance have the same compact limit. This proves that the
choice of a point of ℍ does not affect the named hitting measure. Left translating
the starting group vertex translates its path limit and pushes forward its law.

For conjugation, the finite support is relabeled by the actual group isomorphism.
Matching one-step probability masses transport the infinite product law; induction
identifies all finite-time positions. Continuity of the compact action and uniqueness
of limits then identify the chosen boundary maps almost surely. Consequently the
normalized hitting measure is exactly the inverse-matrix pushforward. Combining
this with visual covariance proves equivalent singularity conclusions. It does
not supply the still-missing rigidity, Martin/Naïm, or invariant-current inputs.

The current's domain is now the open complement of the diagonal in
(ℝ∪{∞})², with its actual diagonal SL(2,ℝ) action. The product of the backward
and forward hitting probabilities restricts to a probability there because the
forward law has no atoms. Weighting it by a real kernel is automatically
sigma-finite; continuity on this open pair space suffices for local finiteness
and regularity, even when total mass is infinite.

The change-of-variables argument now uses the actual Radon–Nikodym derivatives
of the stationary marginals, which need be positive only almost everywhere.
A kernel covariance identity in these derivatives proves invariance on the
pair space. This is a conditional implication, not a construction of the full
Naïm kernel or its identification with Martin limits. Those analytic boundary
results and the initial rigidity theorem remain essential gaps. Cocompact
Liouville ergodicity is now proved.

The Liouville reference itself is now explicit. The compact Cayley map C has
C(∞)=1 and C(x)=(x−i)/(x+i), and its squared Euclidean distance for finite
endpoints is 4(x−y)²/((1+x²)(1+y²)). The density 4π²/dist(Cξ,Cη)² relative to
two visual probabilities at i therefore gives exactly dx dy/(x−y)². The
compact kernel is positive and continuous away from the diagonal, establishing
the current's local finiteness and regularity across infinity as well.

Translations, positive dilations and inversion preserve the real current.
Their matrix factorization proves full Möbius invariance, and the exact chart
measure identity transfers this to the compact pair space. The comparison
with the actual hitting-law current now uses this concrete invariant reference.
Cocompact Liouville ergodicity is now proved. The remaining hitting-law rigidity
and Naïm-kernel identification have not been replaced by an assumed
proportionality conclusion.

The ergodicity work now has a checked dynamical core. The Mautner contraction
argument proves that one positive diagonal time has the same fixed vectors
as the entire group. Applied to L² indicators, this gives ergodicity of the
diagonal time map on a finite Haar quotient, whose full-group ergodicity is
proved separately by lifting null sets through a fundamental domain. The
right invariance of Haar measure is also derived, using perfection of SL(2,ℝ).
The finite fundamental domain, Haar/Liouville measure-class correspondence,
and measurable descent are now constructed. Their combination in
`CocompactLiouvilleErgodicity.lean` establishes ergodicity of the lattice action
on the actual `BoundaryPair` Liouville current.

Cocompactness now supplies the actual Haar quotient used in this argument.
The proper orbit map lifts a compact covering set in ℍ to a compact set in
SL(2,ℝ); inversion gives a compact cover of the right-coset quotient. Finitely
many local sheets of the quotient covering map yield a measurable transversal,
contained in a compact set. Restricting Haar measure to this domain and pushing
it to the quotient gives the checked finite, nonzero invariant measure with
ergodic diagonal times.

The inverse-frame map g ↦ g⁻¹·(∞,0) is measurable, unchanged by left diagonal
multiplication, and equivariant for inverse right multiplication. Explicit
matrices prove transitivity of the full action on boundary pairs. A Fubini
argument then identifies the null sets of its Haar pushforward with those of
the concrete Liouville current. The measurable descent and transfer of diagonal
ergodicity back to boundary pairs are now proved in the final modules.

The Liouville ergodicity obligation is now proved in the cocompact case.
For a countable lattice, intersecting inverse translates replaces an
almost-invariant set by an exactly invariant measurable representative.
Its image in the group quotient is measurable, and quotient null-set
identification transports its almost-invariance under a positive diagonal
time. The proved time-map ergodicity makes it null or conull. Lifting this
conclusion and using the Haar endpoint measure class proves ergodicity of
the lattice action on the explicit Liouville current.

`compactLiouvilleCurrent_ergodic` assumes only the original discreteness and
surface-cocompactness hypotheses. `geometricKernelCurrent_eq_liouville_cocompact`
uses it in current comparison, leaving the initial hitting-law rigidity and
actual Naïm-kernel construction/identification as the deep remaining inputs.
The full singularity theorem and noncocompact extension are still unfinished.

## Hitting-measure ergodicity and nonsingularity

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `IndependentShift.lean` | Constructs a tail-measurable representative of an almost shift-invariant event and proves its probability is zero or one by Kolmogorov's law. | Coordinate independence and almost invariance under every shift are the abstract inputs. |
| `WalkBoundaryErgodicity.lean` | Proves the one-step shift zero–one property for the actual jump law; derives the zero–one property for almost group-invariant boundary sets from the first-step cocycle. | No group-invariance of the hitting measure is asserted. |
| `ErgodicMeasureDichotomy.lean` | For a countable group, an ergodic probability not singular to a quasi-invariant reference is absolutely continuous with respect to it. | Uses countable null-set saturation; no density bound follows. |
| `GeometricHittingErgodicity.lean` | Proves the first-step identity for the constructed geometric limit, hitting-law ergodicity, visual quasi-invariance, and absolute continuity under nonsingularity. | Retains the original discrete-group, positive finite semigroup-generating law, and spectral-gap hypotheses. |
| `ErgodicMeasureFactor.lean` | Transfers ergodicity through an equivariant measurable map and an equivalent probability measure class. | Does not require the pushforward itself to be finite or the probability to be invariant. |
| `CocompactVisualErgodicity.lean` | Identifies the null sets of the first marginal of Liouville current; proves visual ergodicity and equivalence of visual and nonsingular hitting measures in the cocompact case. | Equivalence means equality of null sets, not uniform upper and lower density bounds. |

The new probability argument distinguishes ergodicity of a measure class from
invariance of a measure. A hitting law is generally only quasi-invariant.
Its almost group-invariant events pull back to almost shift-invariant path events.
The limsup of their shifted copies is measurable in the genuine coordinate tail
sigma algebra and agrees with the original event almost everywhere. Kolmogorov's
zero–one law therefore applies without assuming exact equivariance everywhere.

For any visual-null measurable set, its countable group saturation is still
visual-null and is exactly invariant. Hitting-law ergodicity gives this saturation
hitting mass zero or one; mass one would contradict nonsingularity. This proves
absolute continuity. In the cocompact case, endpoint projection transfers the
proved Liouville ergodicity to visual measure, and the same argument with the
measures reversed proves equivalence. The remaining rigidity obligation is
stronger: uniform density bounds and the Green/hyperbolic-distance comparison,
including the connection between the forward and reflected laws.

## Uniform density bounds from a continuous current

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `CompactProductDensity.lean` | On a compact Hausdorff space with a nonatomic probability, an a.e. product identity with a positive continuous off-diagonal function gives common positive lower and finite upper bounds for both factors. | Uses two distinct good sections and a compact cover; no continuity of the marginal densities is assumed. |
| `BoundaryCurrentDensity.lean` | Reconstructs measures with their real Radon–Nikodym densities; derives their scalar product identity from equality of off-diagonal currents. Proves positivity and off-diagonal continuity properties of the zero extension of kernels. | Marginal absolute continuity and the current identity are explicit inputs. |
| `BoundaryCurrentBounds.lean` | Positive scalar current equality gives reverse marginal absolute continuity. Positive continuous kernels then give uniform two-sided a.e. density bounds and the corresponding measure inequalities. | Requires probability marginals absolutely continuous to a nonatomic reference and current equality; it does not construct a Naïm kernel. |
| `CocompactHittingBounds.lean` | Applies proved cocompact ergodicity and current comparison to obtain common two-sided visual bounds for the actual forward and reflected hitting laws. A second theorem obtains the needed absolute continuity from nonsingularity of both laws. | The positive continuous kernel and covariance are still supplied. Forward nonsingularity alone is not asserted to imply reflected nonsingularity. |

The compact density argument fixes two distinct good second-coordinate sections
of the a.e. product identity. Disjoint neighborhoods of their anchors have closed
complements covering the compact boundary. On each complement the kernel ratio,
divided by the positive density at its anchor, has a positive minimum and finite
maximum. These bound the first density almost everywhere; swapping coordinates
bounds the other density. In particular, equality of currents cannot be used to
claim bounds merely from measurable kernel positivity: continuity is used
explicitly on the compact sets away from the anchors.

This supplies an alternative route to the uniform-density part of rigidity once
the actual continuous Naïm kernel, its covariance, and both marginal absolute-
continuity inputs have been established. It leaves the Green-distance comparison,
full Naïm construction, and passage from forward nonsingularity to the
reflected-law input unresolved. The full singularity theorem remains unfinished.

## First-hit domination and the upper Green-distance estimate

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `FirstEntranceHarmonic.lean` | Proves finite-time and full first-hit inequalities for every nonnegative superharmonic function. Applying them to actual stationary Radon–Nikodym kernels gives `F(x,y) y_*ν ≤ x_*ν`. | The full first-hit series uses the existing spectral-gap convergence. The boundary measure is stationary for the positive semigroup-generating law. |
| `GreenFirstHit.lean` | Proves `G(x,y)=F(x,y)G(y,y)` by the checked square-integrable Dirichlet uniqueness theorem; derives the corresponding Green inequality for nonnegative superharmonic functions. | Uses contraction, total jump mass one, and the spectral gap; no Martin identification is assumed. |
| `PoissonDominationDecay.lean` | Proves that `t m_z ≤ B m_i` implies `t ≤ 2 B exp(-d(i,z))`, on both the real and compact boundary models. | Scalars are nonnegative. Uses explicit Poisson densities and the hyperbolic cosh-distance formula. |
| `GreenVisualUpper.lean` | Derives `G(x,y) ≤ (2 b G(e,e)/a) exp(-d(xi,yi))` from `a m_i ≤ ν ≤ b m_i` for a stationary boundary measure, and specializes it to the constructed hitting law. | Requires `a>0`; supplies only the upper half of the Green comparison. |
| `CocompactGreenUpper.lean` | Combines nonsingularity-to-absolute-continuity, cocompact current comparison, uniform density bounds, and first-hit domination to give one common upper comparison constant for the original and reflected walks. | Both hitting-law nonsingularity assumptions and the positive continuous covariant current kernel remain explicit. |

The first-hit proof does not assume that actual stationary derivatives equal
geometric Martin kernels. Their already proved harmonicity suffices. Two-sided
visual bounds imply `a F(e,g) m_(g i) ≤ b m_i`; the Poisson estimate bounds
`a F(e,g)` exponentially. Singleton renewal then supplies the Green estimate,
and left invariance handles arbitrary vertices. The reflected estimate follows
from `checkG(x,y)=G(y,x)` and symmetry of hyperbolic distance. This proves the
upper comparison independently of a lower Green bound; it does not establish
that missing lower bound or the initial density bounds from forward
nonsingularity alone.

## Hyperbolic detours and spectral decay

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `GeometricDetour.lean` | Proves a lower bound for disk separation from bounded hyperbolic triangle excess. A path avoiding the open radius-`R` ball with disk-separated endpoints has at least `δ exp R / (4 exp L)` steps; all shorter killed transition coefficients vanish. | Uses the actual finite jump words and finite jump-length bound. For the excess criterion, endpoints are at hyperbolic distance at least two. |
| `KilledGreenDecay.lean` | Upgrades eventual spectral decay to `‖P^n‖ ≤ C q^n` at every time, with `C>0` and `0<q<1`. A killed kernel with no paths below `N` is bounded by `C q^N/(1-q)`; a real cutoff gives the corresponding exponential bound. | The operator spectral gap and nonnegative jump weights are inputs. The sum and tail identity use proved absolute convergence. |
| `KilledWalkTransport.lean` | Transports path avoidance, killed transition coefficients, and the killed Green series under simultaneous left translation of endpoints and the avoided set. | Purely algebraic; does not assume convergence, symmetry, or invariance of the killed set. |
| `HyperbolicGreenDetour.lean` | Combines the actual geometric cutoff with the spectral tail to obtain `A exp(-c exp R)`, with positive constants uniform over all orbit centers and disk-separated endpoints. Bounded triangle excess supplies separation; every prescribed exponential rate eventually bounds the same Green mass. | No cocompactness or boundary-density assumptions are used. This bounds the absolute Green mass of detours; it does not yet prove a relative Ancona comparison, unique geometric Martin limits, or a continuous Naïm kernel. |

More precisely, write `o=u i`, `X=x i`, and `Y=y i`. If
`d(X,Y)≥2` and `d(X,o)+d(Y,o)-d(X,Y)≤D`, the centered disk coordinates
are separated by at least `exp(-D/2)/4`. For every fixed `D`, positive
constants `A,c`, independent of `R,u,x,y`, therefore bound the Green mass of
paths avoiding the open ball `B(o,R)` by `A exp(-c exp R)`. In particular this
applies when `o` lies on a geodesic between the endpoints. No lower Green bound
has been inferred from this absolute upper bound.

## Coarse Green lower bound and relative detours

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `HyperbolicHarnack.lean` | A fixed bound on hyperbolic displacement gives one Green-row Harnack constant uniform in both starting vertices and the target; comparison iterates along finite orbit chains. | Discreteness makes the bounded-displacement group set finite, retaining stabilizer multiplicities. Uses positive finite support, semigroup generation, and the spectral gap. |
| `MetricChains.lean` | Concatenates finite chains and subdivides any isometric real interval into unit steps, using at most interval length plus two steps. | General metric lemmas; no hyperbolic geometry is assumed. |
| `HyperbolicChains.lean` | Constructs a chain between any two points of the upper half-plane, with jumps at most one and at most `3d+5` steps. | Uses an explicit vertical-horizontal-vertical route and isometric transport, not an assumed geodesic theorem. |
| `CocompactOrbitChains.lean` | Approximates these chains in a `D`-dense orbit, retaining the prescribed group endpoints, to get at most `3d+7` jumps of length at most `2D+1`. Cocompactness supplies such a `D`. | No Green comparison or boundary identification is used. |
| `CocompactGreenLower.lean` | Iterated Harnack comparison gives `G(x,y) ≥ a exp(-b d(xi,yi))` with `a,b>0` for the actual Green kernel. | The exponent is unspecified; this does not give the sharp exponent-one lower bound needed in the rigidity argument. |
| `CocompactRelativeDetour.lean` | For any fixed triangle-excess bound `D`, distance multiplier `B`, and desired rate `K`, proves `G_avoid ≤ exp(-K R) G` and the normalized ratio bound for sufficiently large `R`, uniformly in all orbit centers and eligible endpoints. | Requires endpoint distance between `2` and `B R`. This restriction remains explicit, so the result is not a full Ancona inequality for arbitrary endpoint distances. |

The lower bound requires no nonsingularity or current hypothesis. Finite
semigroup generation supplies positive paths between any bounded-displacement
pair; discreteness makes their comparison constants uniformly bounded. The
orbit chain then gives `G(x,y) ≥ C^(-N)` with `N≤3d+7`. One can take
`a=exp(-7 log C)` and `b=3 log C+1`. In the relative detour estimate, this
exponential lower bound absorbs only an exponential factor, while the avoided
Green mass decays double-exponentially in `R`.

## Finite entrances and global polynomial product comparison

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `FiniteEntranceDecomposition.lean` | Expands vectors supported on a finite set into point masses; identifies the finite scalar action of the actual entrance operator; proves `G(x,y)=G_avoid(x,y)+Σ F_A(x,a)G(a,y)` and bounds the entrance contribution by `G`. | Uses a finite set, nonnegative jump weights of total mass one, and the spectral gap. This is an exact identity for the already constructed path kernels. |
| `CocompactGlobalHarnack.lean` | Compares arbitrary Green rows by `G(z,y) ≤ a exp(b d(xi,zi)) G(x,y)`, with constants uniform in the target. | Uses the proved local Harnack comparison and cocompact orbit chains; no geometric Martin identification is assumed. |
| `GreenProductBounds.lean` | Proves the universal lower product inequality `G(x,u)G(u,y) ≤ G(u,u)G(x,y)`. Local Harnack comparison on a finite entrance set bounds the entrance term by `C² G(x,u)G(u,y)`. | The upper bound retains the killed Green kernel as an explicit additive remainder. |
| `CocompactGreenBall.lean` | Proves finiteness of group vertices in open hyperbolic balls. Derives `G(x,y) ≤ G_avoid(x,y)+a exp(bR)G(x,u)G(u,y)` at every orbit center and every radius. | The cost grows exponentially with the radius; this alone is not an Ancona inequality. |
| `CocompactPolynomialComparison.lean` | Chooses a logarithmic radius which makes the double-exponential avoided mass at most half of the coarse Green lower bound. Obtains `G(x,y) ≤ H (1+d(xi,yi))^p G(x,u)G(u,y)` for bounded triangle excess, including short endpoint distances. | The exponent `p≥0` is unspecified. This module retains polynomial loss; the later geodesic Ancona theorem removes it under the segment-neighborhood condition. The later minimality and compact Martin modules establish geometric boundary identification. |

The finite entrance estimate avoids an extra cardinality loss: the weighted
sum `Σ F_A(x,a)G(a,u)` is at most `G(x,u)`, directly from renewal and
nonnegativity of the killed kernel. The global Harnack estimate controls all
rows inside the ball. Taking `R=log(M(1+d(xi,yi)))` turns its exponential
radius cost into a polynomial in endpoint distance, while the absolute detour
bound becomes small enough to absorb into `G(x,y)/2`. A fixed ball handles
the bounded-distance case, so the final polynomial theorem has only the
triangle-excess condition and no restriction relating endpoint distance to a
chosen radius. The full singularity formalization remains incomplete.

## Finite first/last-entry iteration

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `FiniteLastEntrance.lean` | Proves nonnegativity of reflected weights; transposes the reflected first-entry formula into the original Green kernel's finite last-entry identity and sum bound. | No symmetry is assumed. The remainder is explicitly the reflected killed kernel with reversed endpoints. |
| `LocalTransferIteration.lean` | Proves finite accumulation of relative errors for linear transfers preserving inequalities between successive admissible state sets. Total loss at most `1/2` gives a factor-two comparison. | A general induction theorem with explicit local monotonicity, decreasing potential, error, and terminal comparison inputs. |
| `EntrancePairTransfer.lean` | Constructs the actual finite first/last-entry maps on endpoint-pair functions; proves local monotonicity, exact Green decomposition, and decrease of `G(x,o)G(o,y)`. | Successor-pair membership is required for local comparison; no inequality outside the specified sets is used. |
| `FiniteEntranceIteration.lean` | Instantiates the induction with the actual path kernels. Proves a uniform terminal product bound when the left endpoint is in a fixed hyperbolic neighborhood of the center. | Ball choices, admissible pair sets, successor membership, and small accumulated errors remain explicit inputs. |
| `GeometricEntranceErrors.lean` | Gives one radius threshold for the forward and reflected relative detour estimates, for finite sets equal to the full orbit balls. | Each admissible pair must satisfy bounded triangle excess at the current ball center and endpoint distance between `2` and `B` times its radius. |
| `GeometricEntranceIteration.lean` | Proves that radii bounded below backwards by `R₀+(N-1-n) log 2`, with `R₀≥log 4`, give total error at most `1/2`. Discharges the analytic error hypotheses to yield a uniform product estimate from explicit ball-sequence geometry. | This module is conditional. The later shrinking-axis modules construct the sequence for pairs near opposite axis positions. |

The construction follows the first/last-entry iteration used in
[Gouëzel–Lalley, §4.1, proof of Theorems 4.1 and 4.3](https://www.numdam.org/article/ASENS_2013_4_46_1_131_0.pdf).
The formalization applies the already proved subcritical spectral estimates to
both orientations, without assuming a symmetric walk. The reference guides the construction; no theorem is imported from it as an axiom.

In particular, `geometric_finite_entrance_iteration` proves a precise implication:
given full finite orbit balls, an orientation for each step, and admissible
endpoint-pair sets, its successor-closure, geometric detour, radius-schedule,
and terminal-location hypotheses imply a uniform Green product bound. None
of those geometric hypotheses is packaged as an axiom or asserted to hold
without proof. Their construction is now supplied by the following modules.


## Constructed geodesic Ancona comparison

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `CayleyExcess.lean` | Bounds disk separation above by `4 exp(-excess/2)` and converts positive separation to a triangle-excess bound. Moving a center by `E` costs at most `2E`. | Pure upper-half-plane and metric geometry. |
| `AxisBallSeparation.lean` | Proves the signed vertical ray is unit speed. Opposite balls with a fixed logarithmic margin have triangle excess at most `2 log 32` at their intermediate axis point. | The separation margins are explicit. |
| `AxisBallGeometry.lean` | Gives pair-distance bounds and triangle-excess bounds for orbit centers approximating axis positions within `E`. | Records all approximation errors. |
| `HyperbolicAxisNormalization.lean` | Constructs rotations fixing `i`, moves any point onto the vertical axis by the intermediate value theorem, orients the resulting axis, and joins every pair of points by a unit-speed geodesic line. | No uniqueness theorem for all geodesics is needed or asserted. |
| `ShrinkingAxisInterval.lean` | Halves the longer interval side, proves contraction by `3/4`, finite stopping, and the backwards radius schedule. | Scalar construction with explicit positive stopping threshold. |
| `ShrinkingAxisGeometry.lean` | Constructs admissible pair tubes, proves closure under ball replacements, controls triangle excess and pair distance by `800` times the ball radius, and bounds terminal distance. | Uses fixed orbit-approximation error `E`. |
| `CocompactAxisAncona.lean` | Chooses actual finite orbit balls, proves every iteration hypothesis, and derives a uniform product upper bound for a middle point near an axis segment. | Cocompact, discrete, finite semigroup-generating law, and subcritical spectral radius. No symmetry is assumed. |
| `CocompactGeodesicAncona.lean` | For every fixed `K`, proves a constant `C≥1` and, for each orbit endpoint pair, a unit-speed geodesic joining them such that `(G(x,o)G(o,y))/C ≤ G(x,y) ≤ C G(x,o)G(o,y)` whenever `o i` lies within `K` of a point of its segment. | Ordinary Ancona comparison, not strong Ancona, boundary-limit uniqueness, or the singularity theorem. |

The cut ball has radius one four-hundredth of the current interval length.
Admissible endpoint tubes have radii one fiftieth of their respective distances
from the axis origin, plus `E`. The threshold is chosen before the terminal
Harnack constant, so there is no circular dependence of constants. There is no
remaining polynomial factor in the geodesic Ancona theorem. The following
modules now extend it to bounded triangle excess and derive quantitative
properties of actual geometric subsequential limits. Full geometric Martin
identification and the continuous Naïm kernel remain unfinished.


## Geometric Martin clusters and positive Naïm subsequences

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `AxisTriangleExcess.lean` | Uses an explicit hyperbolic cosine formula to find a point on the endpoint segment within `D/2+log 4` of any point with triangle excess at most `D`. | Holds for arbitrary triples in the upper half-plane. |
| `CocompactExcessAncona.lean` | Derives a uniform Green product bound for arbitrary triples with bounded triangle excess, and for disk-separated endpoint pairs at basepoint `i`. | Cocompact setting with finite positive semigroup-generating support and spectral radius below one. No symmetry. |
| `NaimAnconaBounds.lean` | Proves the universal lower bound `1/G(e,e)` on finite Naïm quotients and a uniform finite upper bound for disk-separated pairs. Distinct disk limits give positive finite subsequential quotient limits. | Subsequence convergence, not a unique full limit. |
| `CayleyRealBoundary.lean` | Extends the Cayley coordinate continuously and injectively to the finite real boundary chart. | The point at infinity is not included in this chart. |
| `GeometricNaimSubsequence.lean` | Gives positive finite Naïm subsequential limits for arbitrary approaches to distinct finite real endpoints. For the actual orbit rays, chooses a common subsequence also giving positive normalized harmonic forward/reflected Martin functions. | No density or current assumptions; uniqueness and continuity remain unproved. |
| `GreenVanishing.lean` | Proves Green-column square summability and that rows and columns vanish at infinity. A scalar product estimate converts Green decay to divergence of a Martin function. | Uses the checked counting-L² Green operator. |
| `RayMartinBounds.lean` | Proves a uniform reciprocal-Green bound for finite ray Martin quotients and every subsequential ray limit. Each ray has a positive normalized harmonic limit which grows to infinity on that ray. | Does not assume or prove uniqueness at a fixed endpoint. |
| `RayMartinSeparation.lean` | Proves every limit from one ray tends to zero on each different finite-boundary ray. Limits coming from different endpoints cannot be equal. | Separates directions but does not make each cluster set a singleton. |
| `RayMartinClusters.lean` | Defines all subsequential limits on each chosen ray; proves nonemptiness, inclusion in the actual abstract Martin boundary, and disjointness for distinct finite endpoints. | No continuous boundary map or full geometric identification is asserted. |

The ray estimate is `1/C ≤ G(e,x_m) H(x_m) ≤ G(e,e)`, with one
constant for all ray directions. Square-summable Green rows give
`G(e,x_m) → 0`, hence growth of `H` on its own ray. Ancona comparison
between separated rays bounds a different limit by a constant times
`G(x_m,e)`, which tends to zero by Green-column square summability.
Uniqueness and full convergence along each chosen ray are now proved in the
minimality modules described below. The later finite-chart modules now also prove arbitrary-approach convergence
and continuity. The compact extension is proved below; the full Naïm limit remains open. The full singularity theorem
is still not formalized.


## Killed domains and the harmonic contraction mechanism

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `CountingKernel.lean` | Expands arbitrary bounded counting-L² operators by their matrix coefficients and proves summability; identifies adjoint rows and restricted point masses. | Uses actual L² inner products and integrability. |
| `EntranceRepresentation.lean` | Identifies the actual first-entrance extension with its absolutely convergent sum for arbitrary, possibly infinite, entrance sets. Every L² function harmonic outside the set equals this extension of its boundary values. | Harmonicity is a stated hypothesis on the actual Markov operator. |
| `RelativeGreenEntrance.lean` | Proves the exact decomposition of `G_A` through additional killing on `B`, with entrance coefficients `F_(A∪B)`. Proves absolute summability, the finite-set version, monotonicity under killing, singleton renewal, and the lower product inequality inside any killed domain. | No geometric regularity or relative Ancona upper bound is assumed. |
| `HarmonicEntranceComparison.lean` | Converts comparison of two actual entrance-kernel rows into comparison of all real L² harmonic functions with nonnegative boundary data, including normalized functions. | The entrance-row comparison is still input. |
| `CommonSubtraction.lean` | Defines the common-removal recursion, proves its basepoint values, cancellation between equally normalized inputs, positivity under admissible removals, and geometric contraction on nested domains. A two-sided comparison with constant `C` yields removal fraction `1/C²`. | Local comparison/admissibility is explicit; this generic iteration alone is not strong Ancona. |
| `KilledGreenSubtraction.lean` | Constructs normalized actual killed Green kernels, proves L² membership and harmonicity away from the killing set and pole, and proves finite subtraction preserves those properties. Instantiates the contraction theorem with these kernels. | Selected normalizers must be nonzero. Uniform boundary-Harnack estimates for the geometric domains remain unproved. |

Writing `G_A` for paths killed on `A`, the checked relative identity is
`G_A(x,y) = G_(A∪B)(x,y) + Σ_b F_(A∪B)(x,b) G_A(b,y)`.
Only `b∈B\A` contribute, and the series is absolutely convergent. Thus
`G_A(x,u)G_A(u,y) ≤ G_A(u,u)G_A(x,y)` also holds without symmetry.

The contraction mechanism follows the common-subtraction argument in
[Gouëzel–Lalley, §4.2](https://www.numdam.org/article/ASENS_2013_4_46_1_131_0.pdf).
For equally normalized inputs it subtracts identical terms. If each removal
captures at least the fraction `1/C²` while preserving nonnegativity, the
remaining difference is bounded by `(1-1/C²)^N (f+g)`. The missing work is to
construct the nested geometric domains and prove the relative kernel estimates
which supply these uniform comparisons. No strong Ancona estimate or full
geometric Martin/Naïm identification is claimed. The separate minimality route
below now proves uniqueness on the chosen orbit rays.

## Relative last exit and explicit semicircular barriers

| File | Proven statements | Explicit boundary |
| --- | --- | --- |
| `KilledGreenReflection.lean` | Pairs the exterior Green equations and proves `G_check,A(x,y)=G_A(y,x)` for every killing set. | Does not require symmetry of the walk. |
| `RelativeLastEntrance.lean` | Transposes the relative entrance identity into the last-entrance identity, including absolute convergence and a finite-set version. | The reflected first-entrance coefficient is the actual path kernel. |
| `EntranceFinalJump.lean` | Proves `F_A(x,a)=1_(x=a)+Σ_g μ(g)G_A(x,ag⁻¹)` for `a∈A`, using Dirichlet uniqueness. | Includes the time-zero contribution and the correct right-walk predecessors. |
| `RelativeExitFlux.lean` | Constructs nonnegative last-exit coefficients, proves absolute convergence and the finite/infinite sum interchange, and factors first entrance through the additional stopping set. | Both killing sets are retained throughout. |
| `RelativeBoundaryComparison.lean` | Transfers Green row bounds on `B\\A` to entrance and harmonic-function bounds when the direct term vanishes. | Relative Green comparison and interception are explicit hypotheses. |
| `CoordinateBarrier.lean` | A coordinate with jump changes at most `L` has separating layers of width `L`. A further one-jump gap proves interception of first entrances. | No stochastic limit or geometric estimate is assumed for this separation argument. |
| `RadialCoordinate.lean` | Proves that `log |z|` is 1-Lipschitz for hyperbolic distance, has value `t` on the axis at height `exp(t)`, and obeys the actual finite jump bound in every isometric chart. | Uses a half-difference of two logarithmic heights. |
| `RadialBarrier.lean` | Constructs orbit sublevels and layers bounded by geodesic semicircles; proves path separation, entrance interception, and the resulting conditional harmonic comparison. | Uniform relative Green bounds on these concrete layers still need proof. |

For `D=A∪B`, define
`q_D(a,b)=Σ_g μ(g)F_check,D(ag⁻¹,b)`.
The checked formula is
`F_A(x,a)=F_D(x,a)+Σ_b G_A(x,b)q_D(a,b)` for `a∈A`.
The infinite sum is absolutely convergent; only `b∈B\\A` contribute.
The coordinate-barrier construction now proves the direct term vanishes for
specified semicircular domains, instead of assuming that fact.

The remaining strong-Ancona work includes proving uniform relative Green
comparison on these layers and arranging the domains so that the successive
residual functions meet the checked contraction hypotheses. Positivity and
coarse lower bounds for normalizers in deep axis tubes are now proved below.

## Interior killed Green bounds and relative detours

| File | Proven statements | Scope |
| --- | --- | --- |
| `CoordinateExcursion.lean` | Bounds coordinate displacement along finite words and proves killing removes no paths shorter than the round trip to a sublevel. | The cutoff uses both endpoint depths and the actual permitted jumps. |
| `GreenKillingLoss.lean` | Expresses `G-G_A` as a convergent sum of removed transition mass and bounds it by a spectral tail. | Estimates the loss through killing, rather than the surviving Green mass. |
| `CoordinateGreenLoss.lean` | Gives uniform constants `C,c>0` with `G(x,y)-G_A(x,y) ≤ C exp(-c(h(x)+h(y)-2r))`. | Valid when `A⊆{h≤r}` and the coordinate has a fixed positive jump bound. |
| `InteriorKilledGreen.lean` | Proves uniform positive local lower bounds and local Harnack comparison for killed Green kernels sufficiently deep in coordinate domains. | Uses discreteness, semigroup generation, and the spectral gap. The Harnack conclusion holds for every target. |
| `RadialKilledGreen.lean` | Applies those estimates to the actual semicircular domains in every isometric chart. | Constants are independent of the chart and boundary level. |
| `AxisOrbitChain.lean` | Constructs short orbit chains following axis intervals and preserves a lower radial depth at every vertex. | Assumes the proved cocompact orbit-cover bound and retains prescribed endpoint vertices. |
| `KilledGreenChains.lean` | Proves the surviving diagonal bound and iterates local Harnack comparison into an exponential lower bound along chains. | All Green values are killed on the same set. |
| `CocompactRadialLower.lean` | Gives a coarse exponential killed Green lower bound, hence strict positivity, for endpoints in a fixed axis tube deep inside a radial domain. | The segment can have arbitrary length; the tube radius and depth buffer are fixed. |
| `RadialRelativeDetour.lean` | Proves relative detour error at most `exp(-KR)` for every prescribed rate `K`, normalized by the actual killed Green kernel. | Requires a fixed deep axis tube, segment length at most `BR`, and bounded triangle excess at the detour center. |

The lower bound is `G_A(x,y) ≥ α exp(-β(b-a))` for endpoints within a fixed
distance of axis parameters `a≤b`, provided `a` is a fixed distance beyond the
killing level. It proves positivity of the corresponding Green normalizers
uniformly over arbitrary segment lengths. The exponent is not asserted to be one.

These estimates do not yet give uniform relative Ancona comparison for all
points of an infinite barrier layer. Extending the geometry and entrance
iteration to that scope, then applying the contraction to the actual residuals,
remains open in the contraction route to continuity of the geometric kernels.

## Whole radial domains and relative entrance iteration

| File | Proven statements | Scope |
| --- | --- | --- |
| `RadialGeodesicConvexity.lean` | Computes squared radius along arbitrary Möbius images of the axis and proves radial superlevels are geodesically convex. Constructs a geodesic retaining a common endpoint depth. | No fixed-tube assumption is used. |
| `AxisOrbitChain.lean` | Strengthened to retain the distance of every chain vertex to the finite axis segment. The previous radial-depth theorem follows as a corollary. | Existing callers keep their original statements. |
| `DeepRadialOrbitChain.lean` | Constructs short orbit chains between arbitrary endpoints above a radial level, losing only the orbit-cover radius in depth. | The endpoints need not be near the chart axis. |
| `DeepRadialGreenLower.lean` | Proves `G_A(x,y) ≥ α exp(-β d(xi,yi))` and positivity for every pair beyond one fixed depth buffer. | Uniform in both endpoints, chart, and killing level; exponent one is not claimed. |
| `DeepRadialRelativeDetour.lean` | Removes the fixed-tube restriction from the relative detour estimate, with normalization by the actual killed Green kernel. | Endpoint distance is at most `BR`, excess is bounded, and both endpoints have the stated depth. |
| `RelativePairTransfer.lean` | Constructs first/last-entrance transfers retaining the original killing set, proves the exact Green decomposition, and proves the product potential decreases. | Uses the actual reflected law for right-endpoint updates. |
| `RelativeEntranceIteration.lean` | Proves the finite relative iteration and the terminal killed product bound for nearby deep vertices. | A geometric sequence satisfying all successor and error conditions must still be constructed. |
| `RadialCayleySeparation.lean` | Proves uniform disk separation and bounded triangle excess for entire radial regions separated by a fixed gap, in all axis scales. | Covers points arbitrarily close to the real boundary. |
| `RadialGreenComparison.lean` | Applies ordinary Ancona to give a uniform unrestricted Green product bound across those whole regions. | This theorem concerns `G`; the corresponding `G_A` comparison is still required. |

The lower-bound and relative-detour stages now apply throughout the deep radial
domains. The full shrinking construction is instantiated below under a linear
clearance condition. Comparison on the full barriers still requires a result
without that length-dependent condition, before the checked common-subtraction
argument supplies strong Ancona and unique geometric limits.

## Relative ball bounds and Ancona with explicit clearance

| File | Proven statements | Scope |
| --- | --- | --- |
| `RelativeGreenProductBounds.lean` | Bounds the retained finite entrance mass by the killed Green product through a center. | Keeps `G_(A∪B)` as the exact additive error and has no cardinality loss. |
| `DeepRadialHarnack.lean` | Gives row comparison with cost exponential in displacement, for all starts in one fixed deep radial region. | The depth buffer is independent of displacement; the target is arbitrary. |
| `DeepRadialGreenBall.lean` | Gives a product comparison through an actual finite orbit ball, with exponential cost in its radius. | Center depth must exceed the radius plus the fixed buffer. |
| `DeepRadialPolynomialComparison.lean` | Absorbs the detour error at logarithmic radius to obtain a polynomial relative product bound. | Retains an explicit logarithmic clearance condition at the intermediate vertex. |
| `ShrinkingRadialDepth.lean` | Proves both interval sides decrease and every admissible pair of the shrinking construction retains the needed depth. | Initial axis depth includes the full tube allowance `(l+r)/50+E`. |
| `DeepRadialAxisAncona.lean` | Constructs all shrinking balls and discharges successor, depth, relative-error, and terminal conditions. Gives uniform relative Ancona upper comparison for actual segment endpoints. | Endpoint radial depth must be at least the killing level plus a fixed constant and `1/50` of segment length. |

The uniform conclusion is `G_A(x,y) ≤ C G_A(x,o)G_A(o,y)`, where `C` is
independent of segment length and the domain chart. The additional clearance
hypothesis is still length-dependent. It has **not** been proved for all points
of the infinite barriers used by the strong-Ancona argument. Removing or replacing
that restriction and instantiating the residual-function comparisons remain
open in this route. The following independent argument proves ray Martin
uniqueness without using those relative estimates.


## Minimality, uniqueness, and full convergence on cocompact rays

| File | Proven statements | Scope |
| --- | --- | --- |
| `EventualOscillation.lean` | A bounded ratio with uniform lower and upper eventual comparisons along a sequence is constant. | Starting indices may depend on the evaluation state. |
| `HarmonicMinimality.lean` | A uniform positive H-transform hitting lower bound implies minimality of H in the positive harmonic cone. | The hitting lower bound is explicit here and discharged for actual rays below. |
| `RayTailExcess.lean` | Along any geodesic ray, distance from a fixed point minus ray time is decreasing and bounded below; its tails have triangle excess at most one. Transfers this to the chosen orbit rays. | The excess constant is uniform; the tail start may depend on the fixed point. |
| `RayMartinMinimality.lean` | Ordinary Ancona gives the required eventual Green comparison; every actual cocompact ray cluster function is minimal. | No relative Ancona hypothesis or assumed geometric identification. |
| `RayMartinUniqueness.lean` | Uniform domination of ray cluster functions, combined with minimality and normalization, proves each ray cluster set is a singleton. | Applies to every finite real endpoint and its chosen orbit ray. |
| `RayMartinConvergence.lean` | Proves full pointwise convergence of the ray Martin quotients and constructs an injective map from finite real directions into the actual Martin boundary. | Does not yet prove continuity, surjectivity, convergence under arbitrary boundary approaches, or a full Naïm limit. |

The minimality proof applies Green first-hit domination to `f-mH` and `MH-f`,
where `m` and `M` are the infimum and supremum of `f/H`. The uniform transformed
hitting bound forces `M=m`. Ordinary Ancona and the ray-tail excess estimate
supply that bound for every actual cluster function. Thus ray uniqueness no
longer depends on removing the clearance condition in the relative estimates.
The full singularity theorem remains unfinished.


## Arbitrary finite-boundary approaches and continuous Martin kernels

| File | Proven statements | Scope |
| --- | --- | --- |
| `BoundaryRadialChart.lean` | Constructs a chart carrying each chosen ray exactly to the vertical axis; proves radial escape for every approach to its finite endpoint. | Includes tangential approaches; no rate or bounded-distance assumption. |
| `BoundaryMartinComparison.lean` | Applies ordinary radial Ancona to arbitrary pointwise Martin limits and dominates them by the minimal ray function. | All comparison constants needed for domination are proved. |
| `GeometricMartinConvergence.lean` | Identifies every such limit with the ray Martin point and proves full pointwise convergence along every sequence approaching a finite real endpoint. | The endpoint may be any real number; extension to infinity remains separate. |
| `GeometricMartinContinuity.lean` | Proves continuity of every kernel coordinate and of the map into the actual Martin boundary. | Uses diagonal orbit approximations and the proved arbitrary-approach convergence. |
| `GeometricMartinCovariance.lean` | Proves equivariance with the actual Martin action and the normalized kernel covariance formula. | Source and image coordinates must be finite, expressed by the nonzero Möbius denominator. |

These results discharge the finite real-chart uniqueness and continuity
obligations without strong Ancona or relative killed-domain estimates.
The compact boundary identification and hitting-law derivative identification
are now proved below. The full continuous Naïm kernel, sharp lower Green
estimate, and final singularity assembly remain.


## The full compact geometric Martin identification

| File | Proven statements | Scope |
| --- | --- | --- |
| `CompactMartinChart.lean` | Moves any boundary point, including infinity, into a finite chart by an actual group element and transports arbitrary-approach Martin convergence. | Uses the existing hypothesis that the group orbit of infinity is infinite. |
| `CompactMartinMap.lean` | Constructs the actual Martin point on the whole real projective line, proves full convergence along arbitrary approaches, and proves chart independence. | Agrees exactly with the finite real-chart map. |
| `CompactMartinContinuity.lean` | Proves coordinate continuity and continuity into the actual Martin boundary on the entire compact boundary. | Includes infinity. |
| `GeometricMartinHomeomorph.lean` | Proves injectivity by a common finite chart, surjectivity by escaping finite-pole approximations, and constructs the actual homeomorphism. | No Martin identification axiom is assumed. |
| `CompactMartinCovariance.lean` | Proves equivariance and normalized kernel covariance for all group elements and all compact boundary points. | Includes poles and infinity without exceptions. |
| `CompactMartinMinimality.lean` | Proves that normalized translation preserves minimality, then that every compact geometric kernel and every abstract Martin boundary point is minimal. | Uses the already proved finite-chart minimality and surjectivity. |

The homeomorphism theorem assumes discreteness and cocompactness, positive
finite jump weights of total mass one, semigroup generation, the spectral gap,
and an infinite orbit of infinity. The latter is part of the infinite-boundary-
orbit hypothesis already used by the target argument. The theorem identifies
the full **Martin** boundary. The following last-exit argument identifies the
actual hitting-measure derivatives. The full continuous Naïm kernel and the
singularity theorem remain unfinished.


## Actual hitting derivatives identified with Martin kernels

| File | Proven statements | Scope |
| --- | --- | --- |
| `WalkPrefixTail.lean` | Proves independence of any finite prefix, and its endpoint, from the shifted future under the actual infinite walk law. | Deterministic-time independence; no stopping-time assertion is assumed. |
| `WalkLastExit.lean` | Constructs measurable last-exit events, proves their disjointness, and computes their probabilities as transition weight times escape probability, then Green weight times escape probability. | The escape event forbids returns at positive times. |
| `FiniteLastExitLaw.lean` | Constructs the actual finite last-exit PMF, proves total mass one, and proves exact change of start by the finite Martin quotient. | The finite set contains both starts; no division by a possibly zero escape probability occurs. |
| `FiniteLastExitVertex.lean` | Constructs a measurable last-exit vertex on the original path space and proves its law is the last-exit PMF. | The starting-point fallback is confined to a null event under transience. |
| `LastExitConvergence.lean` | Constructs finite exhaustions containing prescribed states and proves selected last-exit vertices inherit the path's compactification limit. | Exhaustion need not be monotone. |
| `LastExitExpectation.lean` | Proves the exact integral change-of-start formula for arbitrary real tests of finite last-exit vertices. | Integrability follows from their finite range. |
| `GeometricLastExitConvergence.lean` | Proves almost-sure geometric convergence of these vertices and convergence of the finite Martin factors to the constructed kernel at the actual hitting point. | Uses the already proved arbitrary-approach Martin theorem. |
| `HittingMartinIntegral.lean` | Passes change of start to actual boundary expectations for bounded continuous tests on the sphere. | Uniform Harnack bounds supply dominated convergence. |
| `HittingMartinDensity.lean` | Proves exact equality `x_*ν = K(x,·)ν`, then identifies the extended and real actual Radon–Nikodym derivatives. | No Martin–hitting identification assumption is used. |
| `HittingMartinIdentification.lean` | Extends the density formula to every geometric base point, identifies all group coordinates on one full-measure set, and proves the resulting derivative functions are minimal actual Martin boundary points. | Same cocompact and infinite-orbit hypotheses as the compact Martin construction. |

For a finite set `A`, the last-exit mass at `a` is `G(x,a)e_A(a)`.
Changing the starting point therefore multiplies this mass by `G(x,a)/G(1,a)`.
As the sets exhaust the group, last-exit vertices converge to the actual hitting
point. The proved uniform bounds on each Martin coordinate allow dominated
convergence in the finite integral identity. Bounded continuous sphere tests
then determine the embedded measures; the measurable boundary embedding is
injective on measures. Radon–Nikodym uniqueness gives the stated identification.
Last-exit times are not treated as stopping times anywhere in this argument.

This closes the Martin/hitting-derivative identification obligation. The global
positive continuous Naïm kernel, remaining rigidity inputs, final singularity
assembly, and noncocompact extension remain. The next modules now supply sharp
lower Green comparison from visual bounds and the local Naïm construction.


## Sharp Green comparison from actual hitting-density bounds

| File | Proven statements | Scope |
| --- | --- | --- |
| `VisualPoissonComparison.lean` | Bounds visual Poisson values and measures by exponential displacement and proves full support of compact visual measures. | The exponential has coefficient one in the distance. |
| `HittingMartinBounds.lean` | Two-sided visual measure bounds control translated hitting measures and, using the proved derivative identification and continuity, bound every Martin coordinate by `(b/a) exp(d)`. | Visual bounds are inputs. |
| `GreenMartinLower.lean` | Extends a geodesic past any vertex, constructs escaping orbit approximations, and uses ordinary Ancona to obtain a Martin point with `G(1,x)H(x) ≥ 1/C`. | The constant is uniform in the vertex; no visual bounds or Naïm kernel are used here. |
| `GreenVisualLower.lean` | Combines those results with Martin surjectivity to prove `c exp(-d) ≤ G(x,y)` and combines it with the existing upper bound. | Only forward hitting-density bounds are needed; transposition supplies both reflected Green bounds. |
| `CocompactGreenComparison.lean` | Supplies the exact `GreenDistanceComparison` predicate for both walks from visual bounds, and connects it to the existing conditional continuous-current argument. | The current specialization still assumes its positive continuous covariant kernel and both nonsingular marginals. |
| `CocompactStripMartinLimit.lean` | Discharges the pointwise-coordinate hypotheses of the old dominated strip argument with actual forward/reflected Martin limits; allows independent diverging ray times. | Uses sharp Green comparison, or derives it from forward visual bounds. The following route removes these assumptions. |

## Naïm kernel on opposite boundary sides without rigidity assumptions

| File | Proven statements | Scope |
| --- | --- | --- |
| `StripBoundarySeparation.lean` | Proves a finite nonzero boundary point is uniformly separated in disk coordinates from the entire fixed-width axis strip. Every approach is eventually separated from all strip points at once. | An explicit elementary Cayley-distance estimate; tangential approaches are allowed. |
| `StripGreenDomination.lean` | Ordinary Ancona bounds normalized rows and columns on the strip by constant multiples of `G(1,g)` and `G(g,1)`; proves those envelopes square summable. | No visual bounds, current, sharp Green comparison, or periodic strip decomposition. |
| `StripMartinVectors.lean` | Proves strong convergence in the actual supported counting-L² space along every approach to a finite nonzero endpoint. | Limits have the actual reflected and forward Martin coordinates. |
| `StripNaimKernel.lean` | Defines the named strip Martin vectors and their compressed-inverse kernel. Proves full real and complex Naïm-quotient convergence for every pair of approaches to `ξ<0<η`, independence from the approach, reality of the pairing, and the positive lower bound `1/G(1,1)`. | Discreteness, cocompactness, positive finite probability support, semigroup generation, and the spectral gap suffice. |
| `StripNaimContinuity.lean` | Proves joint continuity of this kernel on the entire negative-positive chart by diagonal orbit approximations. | Global off-diagonal extension and covariance are still required. |

The new domination is `G(x,g)/G(x,1) ≤ C G(1,g)` for every strip vertex `g`
when `x` is sufficiently near a transverse endpoint, and likewise for columns.
The spectral gap already makes the fixed Green row and column square summable.
This proves the infinite separator limit directly from ordinary Ancona and
avoids using a Naïm current to justify its own construction. The remaining
Naïm steps are global chart extension, compatibility, and covariance with the
actual hitting derivatives; they are not asserted by the local construction.


## Cocompact singularity without symmetry (2026-09-24)

The former one-sided gap is closed. `CocompactHittingSingularity.lean` proves
singularity of the actual forward hitting law without symmetry and supplies
the spectral gap from cocompactness and infinite boundary orbits.
`cocompact_forward_and_reflected_singular` gives both conclusions.

The new chain constructs the finite invariant Naïm quotient probability,
identifies the Liouville frame lift with the Haar measure class, builds a
global stable frame section, handles the off-diagonal product by Fubini, and
applies the actual Haar average basins to prove one-sided Naïm rigidity.
`README.md` gives the current module-by-module chain; `DEPENDENCIES.md`
records the remaining noncocompact and group-interface work.

This checkpoint contains 1961 audited declarations in 354 modules. The
transitive audit permits only `propext`, `Classical.choice`, and `Quot.sound`.


## Actual projective walk and nonelementary cocompact theorem (2026-09-24)

The projective interface is now complete for the finite-geometric-orbit
definition of nonelementarity. Ten new modules prove the real center and
quotient actions, discrete/cocompact subgroup lift, two-sign finite probability
lift, semigroup generation through the involutive kernel, one-step and infinite
path projection, identification of the actual projective hitting law, and the
final nonelementary cocompact PSL₂ singularity theorem.

`cocompact_fuchsian_hittingMeasure_singular` has no symmetry, spectral-gap,
chosen-lift, or separate infinite-boundary-orbit assumption. Its real-chart
corollary gives Lebesgue singularity. The almost-sure path convergence and
independence of the choice of boundary-limit version are also checked.

This checkpoint contains 2041 audited declarations in 364 modules. Only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The noncocompact theorem remains unfinished.


## General nonelementary dynamics and actual hitting laws (2026-09-24)

Eight new modules remove compactness from the preliminary dynamics and the
construction of the actual projective hitting law:

- `EllipticCommutator`: trace conjugacy, rotation coordinates, and the two
  explicit sum-of-squares commutator identities.
- `EllipticCommonFixedPoint`: an elliptic element in a group with bounded
  traces forces a common interior fixed point.
- `ParabolicCommonFixedPoint`: explicit repeated-root normalization and the
  common ideal fixed point for the parabolic case.
- `NonelementaryHyperbolic`: bounded-trace fixed-point dichotomy, hyperbolic
  element existence, and the resulting special-linear spectral gap.
- `ProjectiveNonelementaryDynamics`: descend north–south dynamics, construct
  a free subgroup of the original projective group, and prove its spectral gap.
- `ProjectiveStationarity`: sum the two half-weight lifts exactly and transfer
  stationarity and translate equivalence to the original hitting law.
- `FuchsianHittingMeasure`: geometric convergence, stationarity, translate
  equivalence, and uniqueness for arbitrary nonelementary discrete PSL₂ groups.
- `FuchsianLimitSet`: a closed ideal orbit limit set carrying full hitting
  probability, and singularity under an explicit visual-nullity hypothesis.

This checkpoint adds 38 declarations, for 2079 declarations in 372 modules.
No compactness, symmetry, assumed spectral gap, or selected hyperbolic element
is a hypothesis of the new general hitting-law result. Singularity for all
noncocompact groups is still unfinished. The audit permits only `propext`,
`Classical.choice`, and `Quot.sound`.


## Green/word comparison and parabolic obstruction (2026-09-24)

Eight new modules add 61 declarations toward the noncocompact case:

- `JumpDistance`: shortest actual permitted paths, left invariance, triangle
  inequality, and uniform comparison between finite admissible supports.
- `WordDistance`: inverse-closed support, symmetric word-distance laws, and
  comparison with the original directed jump distance.
- `GreenJumpBounds`: normalized Green lower bounds from shortest positive
  paths and upper bounds from the spectral tail below which paths cannot arrive.
- `GreenDistance`: the logarithmic normalized Green function, nonnegativity,
  left invariance, directed triangle inequality, and jump-length comparison.
- `GreenWordComparison`: two-sided linear word-distance bounds, also for the
  original nonelementary projective walk without an assumed spectral gap.
- `ParabolicDisplacement`: actual horizontal translation powers, logarithmic
  displacement, sublinear limits at every basepoint, and conjugacy invariance.
- `GreenSublinearObstruction`: incompatibility of linear word growth with
  bounded Green/sublinear-geometric comparison.
- `ProjectiveParabolic`: squared-trace-four projective normalization, both
  lift signs, sublinear displacement from the trace criterion, and the resulting
  Green-comparison obstruction with explicit word-growth hypothesis.

The project now contains 2140 audited declarations in 380 modules. General
parabolic undistortion, the nonsingularity-to-bounded-comparison implication,
and the full noncocompact singularity conclusion remain unfinished. No new
axioms or admitted proofs have been added.


## Finite-index free subgroups and stable Green lengths (2026-09-24)

Eight new modules add 37 declarations:

- `FreeGroupPowerLength`: cyclic reduction and linear power-length growth for
  every nonidentity free-group element, including commutators.
- `SchreierRetraction`: a coset-transversal retraction, its product formula,
  and word-length bounds from finitely many transition terms.
- `FiniteIndexFreeLength`: a uniform bound on free-group length by ambient
  word length and a linear lower bound along a positive power.
- `PowerWordGrowth`: the quotient-and-remainder argument extending that bound
  to every power of any infinite-order element.
- `ParabolicInfiniteOrder`: nontrivial projective shears and their conjugates
  have infinite order; positive powers remain parabolic.
- `VirtuallyFreeParabolic`: Green-comparison and orbit-map obstructions with
  no separate word-growth hypothesis, given a finite-index free subgroup.
- `StableGreenLength`: an actual limit along powers, obtained by Fekete's
  lemma; nonnegativity, upper bounds, homogeneity, vanishing on finite-order
  elements, and positivity under linear word growth.
- `StableParabolicObstruction`: in the virtually free setting, stable Green
  length is zero exactly on finite-order elements. The normalized discrepancy
  from any real multiple of parabolic hyperbolic displacement tends to a
  strictly positive limit, excluding sublinear error.

The project now contains 2177 audited declarations in 388 modules. The
finite-index free-subgroup hypothesis has not yet been derived from the
noncocompact Fuchsian hypotheses. The nonsingularity rigidity implication and
full noncocompact singularity theorem remain unfinished. No new axioms or
admitted proofs have been added.


## Quasiconvexity, parabolics, and the full ideal boundary (2026-09-24)

Seven new modules add 36 declarations:

- `ParabolicOrbitHeight`: the exact shear displacement at any point; no fixed
  interior point; the positive gap for nonzero discrete orbit displacements;
  and bounded height for a discrete group containing a nontrivial shear.
- `ParabolicMidpoint`: the midpoint of opposite parabolic translates has
  height `sqrt(im(z)^2 + t^2)`. The distance-sum segment identity is proved
  from the hyperbolic cosine formula, and the height is at least `abs(t)`.
- `HyperbolicQuasiconvex`: metric-segment quasiconvexity, isometry invariance,
  compatibility with the projective lift, and the normalized cusp obstruction.
- `QuasiconvexParabolic`: the obstruction for arbitrary discrete projective
  groups with a parabolic, independent of finite generation or virtual freeness;
  cocompact orbits are quasiconvex and discrete cocompact groups have no parabolics.
- `FullIdealBoundary`: approach sequences for the compactified closure,
  isometry invariance, conversion to Cayley coordinates, and a universal
  triangle-excess bound from opposite ideal approaches.
- `QuasiconvexFullBoundary`: a full-boundary quasiconvex set lies within
  `D + 2 * log 4` of every hyperbolic point. A uniformly dense projective orbit
  gives a compact quotient, with its closed-ball cover explicitly constructed.
- `FuchsianQuasiconvexReduction`: actual hitting-measure singularity follows
  from quasiconvexity and full limit set. Further reductions display the
  unproved nonsingularity-to-quasiconvexity and null-or-full limit-set premises.

There are now 2213 audited declarations in 395 modules. The geometry of the
quasiconvexity reduction is proved, but the analytic rigidity implication and
limit-set alternative remain unfinished. The full noncocompact singularity
theorem is not claimed. Only the standard logical axioms are permitted.


## Quasiconvex limit-set dichotomy and singularity (2026-09-24)

Nine new modules add 37 declarations:

- `LimitSetDynamics`: actual approach sequences, invariance of the ideal
  orbit limit set, projective Poisson covariance, invariant visual mass, and
  the full-support consequence for closed sets of full visual mass.
- `VisualPoissonOrbit`: visual Harnack comparison at arbitrary basepoints;
  fixed-basepoint complement mass is controlled along nearby orbit points.
- `VerticalRayExcess`: Euclidean escape at infinity, a quantitative cosine
  ratio, a uniform `log 4` triangle-excess bound, and tracking of ideal rays
  by quasiconvex sets.
- `QuasiconvexConical`: the approach `ξ + i exp(-t)` is normalized to the
  vertical ray by the pole matrix and stays uniformly close to the orbit
  whenever `ξ` belongs to its ideal limit set.
- `DensityRescaling`: complement density zero and exact translated-dilation
  Jacobians imply vanishing local mass in each fixed rescaled window.
- `BoundedDensityConcentration`: bounded density controls the window and
  finite mass controls the tail; no pointwise indicator convergence is used.
- `PoissonDensityPoint`: the actual Cauchy/Poisson law is affinely rescaled,
  so vertical Poisson concentration follows at almost every point of every
  measurable real set from Lebesgue's density theorem.
- `QuasiconvexLimitSetDichotomy`: every quasiconvex orbit limit set is
  visual-null or full, without discreteness or finite-generation assumptions.
  Noncocompact quasiconvex orbits necessarily have visual-null limit sets.
- `FuchsianQuasiconvexSingularity`: actual hitting-measure singularity, also
  in the Lebesgue chart, for every discrete nonelementary quasiconvex orbit
  and finite positive semigroup-generating law. The final unrestricted
  reduction needs only the explicit nonsingularity-to-quasiconvexity premise.

There are now 2250 audited declarations in 404 modules. The previous
limit-set-dichotomy gap after quasiconvexity is closed. The analytic rigidity
implication is still unproved, and the unrestricted singularity theorem is
not claimed. No additional axioms or admitted proofs have been added.


## Green comparison to orbit quasiconvexity (2026-09-24)

Six new modules add 22 declarations:

- `QuasigeodesicEnvelope`: finite translated exponential sums, the nearest
  vertex envelope, telescoping Cayley movement, and a chain-length-independent
  movement estimate for linearly separated chains.
- `QuasigeodesicTracking`: an explicit uniform radius and a direct proof that
  endpoint geodesic segments lie near the finite chain, first at i and then
  at every center. Sets admitting such uniform chains are quasiconvex.
- `WordGeodesics`: actual vertex chains for finite words, directed subchain
  length bounds, shortest-subchain equality, and the symmetric index-distance
  formula along shortest word paths.
- `OrbitWordQuasiconvex`: a linear lower word-distance bound implies orbit
  quasiconvexity for isometric actions, including projective subgroups; a bound
  from the identity suffices by left invariance.
- `GreenOrbitQuasiconvex`: a radial upper Green/hyperbolic estimate implies
  quasiconvexity, using the spectral Green/word lower estimate. No such upper
  bound or bounded additive comparison exists in a discrete nonelementary
  group containing a parabolic, without a virtual-freeness hypothesis.
- `FuchsianGreenRigidityReduction`: singularity under the upper Green bound,
  and conditional reductions exposing the still-unproved implication from
  nonsingularity to that bound or to bounded additive comparison.

There are now 2272 audited declarations in 410 modules. The geometric
comparison-to-quasiconvexity implication is proved without an assumed Morse
lemma. The analytic rigidity step remains unproved; the unrestricted theorem
is not claimed. No additional axioms or admitted proofs have been added.


## General stationary cocycles and visual density comparison (2026-09-24)

Ten new modules add 34 declarations:

- `StationaryLogCocycle`: the actual logarithmic derivative in the forward
  action convention, measurability, normalization, additive cocycle identity,
  optional-stopping bounds for logarithms of normalized superharmonic
  functions, and simultaneous directed Green bounds.
- `InvariantConullSet`: every measurable conull set in a countable
  quasi-invariant action contains a measurable invariant conull core.
- `StationaryCocycleDomain`: one exactly invariant conull set supports all
  group cocycle identities and Green bounds pointwise.
- `FuchsianHittingErgodicity`: zero–one for the actual projective hitting law
  and visual absolute continuity under nonsingularity, without compactness.
- `RadonNikodymCoboundary`: reverse quasi-invariance, positive real derivative,
  multiplicative density change, and exact logarithmic coboundary identity.
- `FuchsianLogCocycle`: actual-walk Green bounds, invariant domain, a uniform
  linear word bound, and the visual density coboundary under nonsingularity.
- `LogDensityBounds`: upper and lower measure domination give real derivative
  bounds; exponential measure comparison bounds the logarithmic derivative.
- `VisualLogCocycle`: lower visual measure comparison and hyperbolic
  displacement bounds for the actual visual logarithmic cocycle.
- `InvariantDensityCarrier`: equivalence with the reference restricted to an
  invariant conull positive-density carrier, without claiming global equivalence.
- `FuchsianDensityCocycle`: the carrier for the actual hitting law, geometric
  cocycle bounds with explicit density-error terms, and the conditional bound
  when the log density is essentially bounded.

There are now 2306 audited declarations in 420 modules. The remaining analytic
rigidity is not claimed: uniform density control and the shadow comparison
back to Green distance in the noncocompact setting remain unproved. The full
singularity theorem remains unfinished. No axioms or admitted proofs were added.


## Explicit visual shadows and hitting-measure transfer (2026-09-24)

Nine new modules add 45 declarations:

- `VerticalVisualShadows`: open vertical caps, their real-chart description,
  positive normalized mass, and exact mass at the moving center.
- `VerticalShadowLemma`: the explicit factor `(r²+1)/r²`, pointwise Poisson
  comparison, and two-sided exponential vertical shadow mass bounds.
- `VisualShadows`: chosen oriented axes, transported open caps, covariance of
  measurable images, mass at base and center, and inverse-shadow mass.
- `VisualShadowSize`: cap monotonicity, the `2r/pi` complement bound,
  uniform inverse-shadow fullness, and vanishing mass for escaping centers.
- `VisualShadowDensity`: restricted-measure upper comparisons, their
  covariance, and a local Radon–Nikodym bound.
- `VisualShadowCocycle`: the inverse restricted comparison and the visual
  cocycle's displacement estimate on inverse shadows.
- `FiniteMeasureAbsoluteContinuity`: uniform small-set estimates for a finite
  absolutely continuous measure and transfer of vanishing masses.
- `AbsolutelyContinuousVisualShadows`: uniform inverse-shadow fullness and
  vanishing shadow mass for every absolutely continuous finite measure.
- `FuchsianVisualShadows`: these mass properties for the actual hitting law
  under nonsingularity, and the simultaneous cocycle estimate with its exact
  density coboundary retained.

There are now 2351 audited declarations in 429 modules. These are visual caps
constructed using chosen axes; equivariance of that choice and identification
with harmonic shadows are not claimed. Uniform density control and the
upper Green-distance comparison remain unproved. The unrestricted singularity
theorem remains unfinished; no additional axioms or admitted proofs were added.


## Measure-theoretic shadow rigidity and actual lower Green estimates (2026-09-24)

Ten new modules add 22 declarations:

- `CocycleShadowMeasure`: recovery of the actual derivative by exponentiation,
  the exact image-mass integral, and exponential image/shadow mass bounds.
- `MixedShadowMeasure`: complement-based intersection bounds and exponential
  mixed-shadow estimates, including the one-quarter-complement specialization.
- `ShadowMagnitudeComparison`: logarithmic mass errors, comparison of log
  masses under measure domination, and two-sided or one-sided magnitude bounds.
- `StationaryGreenMeasure`: directed Green bounds for image and target-set
  masses of an actual finite stationary measure.
- `FuchsianGreenShadows`: actual Green mass bounds with inverse mass retained,
  uniform lower Green shadow estimates under nonsingularity, and the explicit
  upper-shadow/density interface sufficient for singularity.
- `ShadowRatioRigidity`: a positive shadow-mass ratio limit bounds magnitude
  difference along the entire sequence.
- `ReturnCoverDensityRigidity`: the finite corrected return-cover argument
  bounds log density on its carrier; the cover remains an explicit hypothesis.
- `LogDensityMeasureComparison`: equivalent finite measures with bounded log
  density satisfy two-sided exponential measure comparison.
- `ShadowRigidityFromReturnCover`: the assembled conditional rigidity theorem,
  with shadow, differentiation, and return-cover inputs explicit.
- `FuchsianShadowCorrections`: actual hitting/visual cocycle differences are
  uniformly bounded for any finite correction set under nonsingularity.

There are now 2373 audited declarations in 439 modules. The common
harmonic/Green shadow data, positive ratio-limit sequence, and return cover
needed for the unrestricted walk have not been constructed. No global visual
measure equivalence or upper Green shadow estimate is inferred from absolute
continuity or from the lower estimate. The general singularity theorem remains
unfinished. No additional axioms or admitted proofs were added.


## Invariant carrier matching and return-cover construction (2026-09-24)

Ten new modules add 26 declarations:

- `InvariantRestrictionCocycle`: derivative preservation under common
  restriction, conull reference restriction, commutation with translation,
  and preservation of quasi-invariance, densities, and log cocycles.
- `InvariantVisualShadows`: visual cocycle and mass estimates on an invariant
  carrier, inverse complement bounds, and uniformly positive inverse mass.
- `InvariantVisualShadowComparison`: uniform exponential visual mass bounds
  and cocycle error with the carrier mass absorbed into the constant.
- `FuchsianVisualCarrier`: the matched invariant equivalent carrier for the
  actual nonsingular hitting law, with density/cocycle identities and estimates.
- `VanishingErrorReturnCover`: vanishing set masses exclude eventual
  membership; eventual shadows then yield returns, including finite corrections.
- `ShadowReturnConcentration`: quantitative transfer of relative shadow error
  to absolute inverse error, and its convergence to zero.
- `ShrinkingExceptionalSets`: eventual membership away from exceptional sets
  and finite corrected coverage by compactness and orbit escape.
- `AdjustableExceptionalCover`: a neighborhood can be avoided by finitely
  many corrections, and one sufficiently large shadow parameter gives coverage.
- `ConcentratingShadowReturnCover`: assembly of relative concentration and
  exceptional-set coverage into a finite corrected return cover, with the
  adjustable-parameter version retaining the necessary quantifier order.
- `FuchsianShadowReturnCover`: the construction for the actual walk, with
  countability, quasi-invariance, and finite-set orbit escape supplied internally.

There are now 2399 audited declarations in 449 modules. Visual carrier
matching and the conditional return-cover construction are checked. The
harmonic/mixed shadow family, its uniform cocycle estimates, relative
concentration, and adjustable exceptional-set convergence remain to be proved.
The fixed-parameter shrinking-complement lemma is only a sufficient special
case; no such shrinking is claimed for ordinary fixed-size visual shadows.
The unrestricted singularity theorem remains unfinished. No additional axioms
or admitted proofs were added.


## Visual exceptional-point convergence and mixed returns (2026-09-24)

Six new modules add 16 declarations:

- `VisualShadowFrames`: exact normalized interval images for inverse visual
  complements, compactness of their frame fiber, and subsequence extraction.
- `FrameRealBoundaryContinuity`: the shear parametrization of finite boundary
  points and joint continuity of the frame action on real inputs.
- `VisualShadowExceptionalLimit`: small-interval control for convergent frames
  and exceptional-point subsequences for SL₂ and PSL₂ visual shadows.
- `FuchsianVisualShadowCover`: finite corrected eventual visual coverage for
  every sequence in a nonelementary projective group.
- `MixedVisualExceptionalLimit`: adjoining the proved visual shadow family
  adds at most one exceptional point and yields finite mixed coverage.
- `MixedVisualShadowReturnCover`: corrected mixed returns from the second
  family's cocycle/exceptional data and mixed positivity/concentration.

There are now 2415 audited declarations in 455 modules. The visual part needs
neither cocompactness nor discreteness. The cap parameter is chosen for each
neighborhood before taking the eventual sequence limit; no fixed-size
shrinking assertion is made. Harmonic exceptional-set and cocycle data,
mixed-shadow concentration, and the differentiating sequence still have to be
constructed. The unrestricted singularity theorem remains unfinished.
No additional axioms or admitted proofs were added.


## Actual path concentration and corrected returns (2026-09-24)

Ten new modules add 20 declarations:

- `FiniteIndependentConditioning`: conditional averaging against an independent
  variable when the observed variable has finite range.
- `WalkPrefixFiltration`: the finite-prefix filtration, its tuple pullback,
  exhaustion of the product sigma-algebra, and Levy convergence.
- `WalkBoundaryTimeCocycle`: iteration of the almost-sure first-step relation.
- `WalkPrefixConditioning`: conditional averaging over the actual independent
  infinite tail at arbitrary deterministic time.
- `WalkBoundaryConcentration`: identification of translated boundary event
  probabilities with conditional expectations and almost-sure concentration.
- `FuchsianBoundaryConcentration`: first-step equivariance of the original
  selector, event/complement concentration, and transfer to dominated finite
  reference measures, without cocompactness.
- `TranslatedConcentrationReturnCover`: return errors are bounded by the
  translated complement mass, yielding corrected shadow returns.
- `FuchsianPathReturnCover`: actual visual pathwise returns and mixed returns
  with only the second family's exceptional convergence left as input.
- `TranslatedShadowConcentration`: the quantitative relative-error bound and
  convergence under cocycle control and uniform positive inverse mass.
- `FuchsianShadowPathConcentration`: this relative concentration for actual
  walk paths and any dominated finite reference measure.

There are now 2435 audited declarations in 465 modules. Relative concentration
along actual paths is derived under geometric shadow controls, and the pathwise
return construction needs no separate relative-concentration premise. The
harmonic shadow estimates and a sufficient comparison of the two shadow masses
along a chosen sequence remain unfinished. The unrestricted singularity theorem
is not claimed. No additional axioms or admitted proofs were added.


## Bounded path comparison without a mass-ratio limit (2026-09-24)

Six new modules add 11 declarations:

- `BoundedDensityWindows`: measurable density windows, existence of one with
  positive mass, and exponential comparison of the restricted measures.
- `ConcentratedShadowComparison`: half-mass concentration, bounded log mass
  ratios, eventual magnitude bounds, and absorption of finite initial segments.
- `InverseShadowMassFromBounds`: inverse mass at least exp(-2C) from lower
  exponential shadow mass and local cocycle control.
- `FuchsianShadowPathComparison`: bounded magnitude discrepancy along almost
  every actual path ending in the density window, with no ratio-limit premise.
- `BoundedSequenceShadowRigidity`: the global density-upgrade argument with
  bounded discrepancy as input. The previous ratio-limit theorem now uses it.
- `FuchsianShadowGeometryRigidity`: internally chosen positive window, path,
  subsequence, and returns give global magnitude rigidity from common shadow
  geometry. A countable parameter family permits choosing the parameter later.

There are now 2446 audited declarations in 471 modules. A separate positive
shadow-mass ratio limit or differentiating sequence is no longer required by
the new actual-walk assembly. Common exponential and cocycle shadow estimates,
finite correction bounds, and eventual geometric coverage remain explicit
inputs. The harmonic/mixed geometry needed to instantiate them is still
unfinished, and unrestricted singularity is not claimed. No additional axioms
or admitted proofs were added.


## Concrete deficit shadows and coverage modulo null sets (2026-09-24)

Seven new modules add 26 declarations:

- `CocycleDeficitShadows`: the actual-cocycle sublevel sets, measurability,
  monotonicity, fixed-element exhaustion, local error, and mass estimates.
- `FuchsianGreenDeficitShadows`: specialization to the original hitting and
  Green data, simultaneous error bounds, and an element-dependent conull bound.
- `FuchsianMixedDeficitShadows`: the countable N/1/(N+1) mixed family,
  cofinality, local harmonic bounds, and conditional pointwise coverage.
- `ShadowEstimatesFromInverseMass`: absorption of positive inverse mass into
  the exponential/cocycle constant C-log c.
- `FuchsianMixedDeficitEstimates`: hitting and invariant-carrier estimates
  for the same concrete mixed sets, with uniform inverse mass explicit.
- `AEExceptionalShadowCover`: finite corrected eventual coverage from
  exceptional containment almost everywhere at sufficiently late times.
- `FuchsianDeficitAECover`: this coverage for the concrete mixed family,
  with visual convergence and countable parameter selection proved internally.

`FuchsianShadowGeometryRigidity` now needs only almost-everywhere geometric
coverage, respecting the null-domain ambiguity of Radon–Nikodym derivatives.
There are now 2472 audited declarations in 478 modules. Uniform inverse mass
and harmonic exceptional-set convergence for the concrete deficit family
remain unproved; pointwise exhaustion does not imply either. The full
singularity theorem remains unfinished. No additional axioms or admitted
proofs were added.


## Deficit compactness and the conditional singularity assembly

- `ExceptionalShadowUniformMass`: subsequential finite-exception containment
  implies uniform inverse-shadow exhaustion for atomless outer-regular laws.
- `FuchsianDeficitCompactness`: names the unproved geometric property; proves
  actual hitting-law atomlessness and derives uniform harmonic inverse mass
  and mixed corrected coverage from that property.
- `FuchsianMixedDeficitUniformMass`: proves uniform mixed inverse exhaustion
  for finite measures absolutely continuous with respect to both laws, and
  positive lower bounds for positive subprobability references.
- `FuchsianSingularityFromDeficitCompactness`: proves singularity conditional
  on the named compactness property, deriving all intermediate shadow
  estimates and correction/coverage hypotheses internally.

There are now 2480 audited declarations in 482 modules. The unrestricted
singularity theorem remains unfinished: `FuchsianDeficitCompactness` is an
explicit hypothesis, not a theorem or an axiom. No admitted proofs or
additional axioms were added.


## Boundary factors and finite entrance deficit bounds

- `BoundaryFactorCocycleBounds`: equivariance of translated pushforwards,
  factor quasi-invariance, and descent of local cocycle deficit bounds by
  restricted measure domination, without pointwise derivative identification.
- `BoundaryFactorDeficitCompactness`: continuous measured factors preserve
  finite-exception deficit compactness, with no injectivity or finite-fiber
  hypothesis.
- `FuchsianDeficitCompactnessOfFactor`: application to a factor carrying an
  auxiliary law to the actual Fuchsian hitting measure.
- `FiniteEntranceHarmonicDeficit`: uniform Green bounds for normalized positive
  superharmonic functions admitting a finite entrance upper representation;
  the stationary-density specialization yields uniform local deficit bounds.
- `FuchsianDeficitFiniteEntrance`: assembles those bounds into the named
  compactness property under the explicit finite entrance representation
  hypothesis.

There are now 2488 audited declarations in 487 modules. The new results do
not construct an auxiliary boundary/factor or the geometric entrance sets,
and do not prove their entrance representation. Deficit compactness and the
unrestricted singularity theorem remain unfinished. No admitted proofs or
additional axioms were added.


## Actual stopping representation and local finite cusp separators

- `BoundaryFirstEntrance`: exact joint first-entrance and boundary-event
  probabilities, at a fixed time and at an arbitrary finite entrance time.
- `FiniteTranslateDensity`: local finite-mixture identities for measures
  imply identities for the actual real translated Radon–Nikodym densities.
- `BoundaryFiniteEntranceRepresentation`: a boundary event forcing a visit
  to a finite set gives the finite entrance mixture and density identity.
- `FuchsianFiniteEntrancePaths`: the actual Fuchsian density representation
  and deficit compactness from the pathwise finite-separator condition.
- `FuchsianFiniteSeparatorRegions`: convergence from every initial vertex,
  trapping of paths avoiding a finite exit set, and deduction of the required
  visit/compactness conditions from deterministic orbit-region geometry.
- `CuspStripFiniteness`: two endpoint height bounds give a positive lower
  height in the axis strip, a compact rectangle, and finite group vertices;
  two normalized parabolic shears supply both bounds internally.

There are now 2505 audited declarations in 493 modules. The probabilistic
entrance representation is proved under the pathwise visit condition. The
remaining geometric task is constructing an adequate family of separators
and trapping regions; the local normalized cusp-strip construction is proved.
The unrestricted singularity theorem remains unfinished, with no admitted
proofs or additional axioms.


## Arbitrary cusp charts and the actual local Green-deficit estimate

- `ParabolicFixedPointCharts`: conjugacy invariance of projective parabolics,
  their nonzero-shear form at infinity, and normalization in a prescribed chart.
- `CuspStripFiniteness`: finiteness for every nonnegative axis-ratio radius
  from the two parabolic shears, extending the finite-jump instance.
- `ProjectiveCuspStrips`: finite strips in the original projective group at
  any two distinct parabolic fixed points, including existence of the chart.
- `FiniteExitEnlargement`: adding one-step predecessors turns a two-endpoint
  separation property into a finite outgoing exit set.
- `ProjectiveCuspExitSets`: the constructed negative cusp half-plane has
  such an exit set for the given finite support.
- `ChartBoundaryArcs`: closed ideal arcs, control of negative-half-plane
  accumulation, and eventual negative-side membership under boundary convergence.
- `FuchsianCuspDeficit`: the actual pathwise visit property, exact density
  entrance formula, and uniform local Green-deficit bound follow from two cusps.

The project now has 2521 declarations in 499 modules. The local cusp bound
has no entrance or separation assumption. An adequate family of such regions
for the unrestricted theorem is still missing. No full singularity conclusion
is claimed beyond the previously completed quasiconvex case.


## Boundary orbit minimality and relative density of parabolic fixed points

- `EndpointImageBounds`: two bounded finite endpoint images control every
  fixed interior image, by an explicit complex-norm estimate.
- `BoundaryOrbitMinimality`: ideal limits lie in every nontrivial closed
  invariant boundary set; every nonelementary boundary orbit accumulates on
  the ideal orbit limit set, without a cocompactness or discreteness hypothesis.
- `ParabolicFixedPointDensity`: existence and conjugacy of parabolic fixed
  points, and accumulation of these points on the entire ideal limit set.
- `ParabolicIdealLimits`: convergence of parabolic powers to their fixed
  point, inclusion of those fixed points in the orbit limit set, and equality
  of their closure with the limit set when a parabolic exists.

The main project now contains 2535 declarations in 503 modules. The global
choice of regions, including control near gaps of the limit set, is still
missing. The standalone sibling `cocompact-proof` project extracts the final
cocompact theorem and its 313 local dependency modules for independent review.


## Singularity for full ideal limit set with a parabolic

- `IntervalBoundaryCharts`: an explicit determinant-one normalizer, chart
  endpoint identities, negative interior coordinates, and containment of the
  closed nonpositive chart arc in the bounded endpoint interval.
- `ShrinkingBoundaryCharts`: dense endpoints give arbitrarily small closed
  arcs around every ideal point; the parabolic specialization uses the proved
  density theorem and the explicit full-limit-set hypothesis.
- `ProjectiveOrbitSubsequences`: compact interior sets have finitely many
  projective group vertices, and every orbit sequence has a subsequence with
  a finite-valued tail or an ideal limit.
- `FuchsianFullLimitCuspSingularity`: constructs the entire family of finite
  path separators, proves deficit compactness, and concludes visual and
  Lebesgue singularity for full ideal limit set with a parabolic.

There are now 2549 declarations in 507 modules. This is a new completed
singularity case with no compactness or entrance assumption. The lattice
reduction to its stated geometric hypotheses and the remaining infinite-
covolume cases are not yet formalized. The standalone cocompact extraction
is unaffected by these additions.


## All parabolic groups and all proper ideal limit sets

- `ProjectiveEndpointHeight`: bounded chart height at both parabolic fixed
  points and ordinary points outside the ideal limit set.
- `DenseStripEndpoints`: a proper ideal limit set has dense complement;
  parabolic and ordinary endpoints together are dense when the limit set is
  proper or a parabolic exists.
- `ProjectiveEndpointStrips`: two endpoint height bounds produce finite
  projective strips and finite outgoing exit sets, including across gaps.
- `FuchsianCuspOrProperLimitSingularity`: full deficit compactness and
  singularity for every parabolic group and every proper ideal limit set,
  with visual and real-chart Lebesgue conclusions and no symmetry assumption.
- `FuchsianFirstKindReduction`: any nonsingular example must have full
  limit set, no parabolics, and noncompact quotient. The final assembly is
  checked conditional on the remaining first-kind structural implication.

There are now 2564 declarations in 512 modules. The remaining obligation is
to prove that a finitely generated discrete nonelementary group with full
ideal limit set and no parabolics is cocompact. It remains an explicit
unproved hypothesis of the structural reduction, not an axiom. The separate
cocompact extraction is unchanged.


## Final Dirichlet-end assembly

Added ProjectiveDirichletCell, DirichletHeightBound, BoundedHeightEndpoints,
ProjectiveDirichletEnds, BoundedHeightSeparators, FuchsianDirichletDeficit,
and FuchsianSingularity. Noncompactness produces a bounded-height endpoint;
full-limit-set minimality makes its orbit dense and supplies finite separators.
The unrestricted finite-support semigroup-generating theorem is assembled
without a geometric classification input. Total: 2591 declarations in 519 modules.
