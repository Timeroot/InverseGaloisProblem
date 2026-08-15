import InverseGalois.Rigidity.RET.Presentation
import InverseGalois.Rigidity.RET.Pi1.Completion
import InverseGalois.Rigidity.RET.Pi1.SphereCompletion
import InverseGalois.Rigidity.RET.Statement
import InverseGalois.Rigidity.RET.Cayley
import InverseGalois.Rigidity.RET.Existence
import InverseGalois.Rigidity.RET.Pi1.CoverCompletion
import InverseGalois.Rigidity.RET.Pi1.FundamentalGroup
import InverseGalois.Rigidity.RET.Pi1.FundamentalGroupCover
import InverseGalois.Rigidity.RET.Pi1.InertiaGenerators
import InverseGalois.Rigidity.RET.Pi1.Etale.Fiber
import InverseGalois.Rigidity.RET.Pi1.Etale.Category
import InverseGalois.Rigidity.RET.Pi1.Etale.Closure
import InverseGalois.Rigidity.RET.Pi1.Etale.Limits
import InverseGalois.Rigidity.RET.Pi1.Etale.Pushout
import InverseGalois.Rigidity.RET.Pi1.Etale.Subalgebra
import InverseGalois.Rigidity.RET.Pi1.Etale.Equalizer
import InverseGalois.Rigidity.RET.Pi1.Etale.DirectSummand
import InverseGalois.Rigidity.RET.Pi1.Etale.FiberFunctor
import InverseGalois.Rigidity.RET.Pi1.Etale.Quotient
import InverseGalois.Rigidity.RET.Pi1.Etale.Connected
import InverseGalois.Rigidity.RET.Pi1.Etale.AbsoluteGalois
import InverseGalois.Rigidity.RET.Pi1.Etale.Equivalence
import InverseGalois.Rigidity.RET.Pi1.Topological.Monodromy
import InverseGalois.Rigidity.RET.Pi1.Topological.MonodromyPath
import InverseGalois.Rigidity.RET.Pi1.Topological.LiftMonodromy
import InverseGalois.Rigidity.RET.Pi1.Topological.QuotientPi1
import InverseGalois.Rigidity.RET.Pi1.Topological.Transport
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleGroup
import InverseGalois.Rigidity.RET.Pi1.Topological.TameCover
import InverseGalois.Rigidity.RET.Pi1.Topological.TameMonodromy
import InverseGalois.Rigidity.RET.Pi1.Topological.SphereBaseCase
import InverseGalois.Rigidity.RET.Pi1.Topological.Wedge
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.Group
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.GenerationGroup
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedPlane
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedSurjective
import InverseGalois.Rigidity.RET.Pi1.Topological.MonodromyNat
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureFill
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureLocal
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.ConvexPunctured
import InverseGalois.Rigidity.RET.Pi1.Topological.ConvexHomotopy
import InverseGalois.Rigidity.RET.Pi1.Topological.BoxLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.SquareLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.RegionVanKampen
import InverseGalois.Rigidity.RET.Pi1.Topological.Spider
import InverseGalois.Rigidity.RET.Pi1.Topological.GroupLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.UnitsDegree
import InverseGalois.Rigidity.RET.Pi1.Topological.Comparison
import InverseGalois.Rigidity.RET.Pi1.AbsoluteGaloisQuotient
import InverseGalois.Rigidity.RET.KummerCover
import InverseGalois.Rigidity.RET.KummerAbelian
import InverseGalois.Rigidity.RET.ArtinFixedField
import InverseGalois.Rigidity.RET.RatFuncGen
import InverseGalois.Rigidity.RET.RatFuncSubst
import InverseGalois.Rigidity.RET.InertiaTransport
import InverseGalois.Rigidity.RET.TamePi1
import InverseGalois.Rigidity.RET.SubCover
import InverseGalois.Rigidity.RET.InertiaGen
import InverseGalois.Rigidity.RET.InertiaSub
import InverseGalois.Rigidity.RET.Unramified
import InverseGalois.Rigidity.RET.Twist
import InverseGalois.Rigidity.RET.KummerInertia
import InverseGalois.Rigidity.RET.MultiKummer
import InverseGalois.Rigidity.RET.LocalKummer
import InverseGalois.Rigidity.RET.MultiKummerInertia
import InverseGalois.Rigidity.RET.Infinity
import InverseGalois.Rigidity.RET.Semilinear
import InverseGalois.Rigidity.RET.SemilinearSub
import InverseGalois.Rigidity.RET.Translate
import InverseGalois.Rigidity.RET.GeomRET
import InverseGalois.Rigidity.RET.SerreCovers
import InverseGalois.Rigidity.RET.DihedralCover
import InverseGalois.Rigidity.RET.ExistenceLowRank
import InverseGalois.Rigidity.RET.ExistenceCyclic
import InverseGalois.Rigidity.RET.SubUnramified
import InverseGalois.Rigidity.RET.FreeAbelianCover
import InverseGalois.Rigidity.RET.ExistenceAbelian
import InverseGalois.Rigidity.RET.KummerNormalForm
import InverseGalois.Rigidity.RET.CyclicKummerModel
import InverseGalois.Rigidity.RET.CyclicBranchLocus
import InverseGalois.Rigidity.RET.CyclicAtInfinity
import InverseGalois.Rigidity.RET.CyclicCycles
import InverseGalois.Rigidity.RET.AbelianGeneration
import InverseGalois.Rigidity.RET.Descent
import InverseGalois.Rigidity.RET.Specialization
import InverseGalois.Rigidity.RET.Genus.Ord
import InverseGalois.Rigidity.RET.Genus.LineOrd
import InverseGalois.Rigidity.RET.Genus.InftyOrd
import InverseGalois.Rigidity.RET.Genus.OrdValuation
import InverseGalois.Rigidity.RET.Genus.Place
import InverseGalois.Rigidity.RET.Genus.Chart
import InverseGalois.Rigidity.RET.Genus.Residue
import InverseGalois.Rigidity.RET.Genus.Degree
import InverseGalois.Rigidity.RET.Genus.Fundamental
import InverseGalois.Rigidity.RET.Genus.Relrank
import InverseGalois.Rigidity.RET.Genus.EtaleDerivation
import InverseGalois.Rigidity.RET.Genus.LineDerivation
import InverseGalois.Rigidity.RET.Genus.Filtration
import InverseGalois.Rigidity.RET.Genus.DerivKernel
import InverseGalois.Rigidity.RET.Genus.ChartIntegral
import InverseGalois.Rigidity.RET.Genus.PoleBound
import InverseGalois.Rigidity.RET.Genus.SimplyConnected
import InverseGalois.Rigidity.RET.Genus.InftyChartRing
import InverseGalois.Rigidity.RET.Genus.UnramifiedAbstract
import InverseGalois.Rigidity.RET.Genus.UnramifiedModel
import InverseGalois.Rigidity.RET.Genus.Unbranched
import InverseGalois.Rigidity.RET.Genus.UnbranchedCover
import InverseGalois.Rigidity.RET.Genus.PlaceInertia
import InverseGalois.Rigidity.RET.Genus.ChartCompare
import InverseGalois.Rigidity.RET.Genus.OrdLog
import InverseGalois.Rigidity.RET.Genus.ResidueField
import InverseGalois.Rigidity.RET.Genus.OrdRamification
import InverseGalois.Rigidity.RET.Genus.LogTameProof
import InverseGalois.Rigidity.RET.Genus.OrdMem
import InverseGalois.Rigidity.RET.Genus.OrdSmul
import InverseGalois.Rigidity.RET.Genus.OrdUltra
import InverseGalois.Rigidity.RET.Genus.OrdDomain
import InverseGalois.Rigidity.RET.NoUnbranchedCover
import InverseGalois.Rigidity.RET.TranslateInfinity
import InverseGalois.Rigidity.RET.InertiaGenerate
import InverseGalois.Rigidity.RET.BaseChart
import InverseGalois.Rigidity.RET.LineParam
import InverseGalois.Rigidity.RET.ChartInertia
import InverseGalois.Rigidity.RET.KummerPullback
import InverseGalois.Rigidity.RET.TwoPointCyclic
import InverseGalois.Rigidity.RET.LowRankRET
import InverseGalois.Rigidity.RET.FreeAbelianUniversal
import InverseGalois.Rigidity.RET.AbelianEmbed
import InverseGalois.Rigidity.RET.AbelianCycles
import InverseGalois.Rigidity.RET.InertiaLift
import InverseGalois.Rigidity.RET.AbelianizedCycles
import InverseGalois.Rigidity.RET.NilpotentCycles
import InverseGalois.Rigidity.RET.AbelianBranchPoints
import InverseGalois.Rigidity.RET.BranchLocus
import InverseGalois.Rigidity.RET.BranchSet
import InverseGalois.Rigidity.RET.AbelianRET
import InverseGalois.Rigidity.RET.DeckGroups
import InverseGalois.Rigidity.RET.MoveInfinity
import InverseGalois.Rigidity.RET.SubcoverProduct
import InverseGalois.Rigidity.RET.Compositum
import InverseGalois.Rigidity.RET.SubcoverBranch
import InverseGalois.Rigidity.RET.Product
import InverseGalois.Rigidity.RET.ProductTranslate
import InverseGalois.Rigidity.RET.ProductGeometric
import InverseGalois.Rigidity.RET.CoverField
import InverseGalois.Rigidity.RET.GeomPi1
import InverseGalois.Rigidity.RET.GeomPi1LowRank
import InverseGalois.Rigidity.RET.GeomPi1Abelian
import InverseGalois.Rigidity.RET.GeomPi1Nilpotent
import InverseGalois.Rigidity.RET.GeomPi1Functorial
import InverseGalois.Rigidity.RET.SeparableUnramified
import InverseGalois.Rigidity.RET.Degeneracy
import InverseGalois.Rigidity.RET.EquationCover
import InverseGalois.Rigidity.RET.LineSubst
import InverseGalois.Rigidity.RET.DihedralBranch
import InverseGalois.Rigidity.RET.DihedralInertia
import InverseGalois.Rigidity.RET.DihedralInfinity
import InverseGalois.Rigidity.RET.DihedralReflection
import InverseGalois.Rigidity.RET.DihedralCycles
import InverseGalois.Rigidity.RET.DihedralExistence
import InverseGalois.Rigidity.RET.RegularBase
import InverseGalois.Rigidity.RET.RegularityConverse
import InverseGalois.Rigidity.RET.RegularCriterion
import InverseGalois.Rigidity.RET.RegularQuadratic
import InverseGalois.Rigidity.RET.RegularCubic
import InverseGalois.Rigidity.RET.RegularQuotient
import InverseGalois.Rigidity.RET.BaseTransport
import InverseGalois.Rigidity.RET.FixedField
import InverseGalois.Rigidity.RET.MobiusAut
import InverseGalois.Rigidity.RET.DihedralLift
import InverseGalois.Rigidity.RET.AnharmonicS3
import InverseGalois.Rigidity.RET.MobiusDihedral
import InverseGalois.Rigidity.RET.MobiusFinite
import InverseGalois.Rigidity.RET.RegularResolvent
import InverseGalois.Rigidity.RET.RegularSymmetric
import InverseGalois.Rigidity.RET.RegularAlternating
import InverseGalois.Rigidity.RET.RegularProduct
import InverseGalois.Rigidity.RET.SemiIsoInertia
import InverseGalois.Rigidity.RET.Scale
import InverseGalois.Rigidity.RET.AffineTransport
import InverseGalois.Rigidity.RET.Inversion
import InverseGalois.Rigidity.RET.ProjectiveTransport
import InverseGalois.Rigidity.RET.DihedralTriple
import InverseGalois.Rigidity.RET.TrivialCycle
import InverseGalois.Rigidity.RET.MonodromyQuotient
import InverseGalois.Rigidity.RET.ThreePoint
import InverseGalois.Rigidity.RET.MobiusRelated
import InverseGalois.Rigidity.RET.CoprimeProduct
import InverseGalois.Rigidity.RET.MonodromyGroup
import InverseGalois.Rigidity.RET.DisjointProduct
import InverseGalois.Rigidity.RET.BraidMonodromy
import InverseGalois.Rigidity.RET.ThreePointEquation
import InverseGalois.Rigidity.RET.SymmetricBranch
import InverseGalois.Rigidity.RET.MorseInertia
import InverseGalois.Rigidity.RET.CuspTransposition
import InverseGalois.Rigidity.RET.MorseSymmetric
import InverseGalois.Rigidity.RET.RamificationBound
import InverseGalois.Rigidity.RET.MorseBranchCycles
import InverseGalois.Rigidity.RET.Trinomial
import InverseGalois.Rigidity.RET.TrinomialOrd
import InverseGalois.Rigidity.RET.GeomFundamental
import InverseGalois.Rigidity.RET.TrinomialCycle
import InverseGalois.Rigidity.RET.TrinomialTotal
import InverseGalois.Rigidity.RET.TotallyRamified
import InverseGalois.Rigidity.RET.SubBranchPoint
import InverseGalois.Rigidity.RET.Analytic.RootCover
import InverseGalois.Rigidity.RET.Analytic.RootFiber
import InverseGalois.Rigidity.RET.Analytic.RootMonodromy
import InverseGalois.Rigidity.RET.Analytic.RootSection
import InverseGalois.Rigidity.RET.Analytic.RootBound
import InverseGalois.Rigidity.RET.Analytic.Growth
import InverseGalois.Rigidity.RET.Analytic.Extension
import InverseGalois.Rigidity.RET.Analytic.Coeff
import InverseGalois.Rigidity.RET.Analytic.Factor
import InverseGalois.Rigidity.RET.Analytic.Sheet
import InverseGalois.Rigidity.RET.Analytic.LocalBranches
import InverseGalois.Rigidity.RET.Analytic.Clopen
import InverseGalois.Rigidity.RET.Analytic.Connected
import InverseGalois.Rigidity.RET.Analytic.PathConnected
import InverseGalois.Rigidity.RET.Analytic.Regular
import InverseGalois.Rigidity.RET.Analytic.DeckMonodromy
import InverseGalois.Rigidity.RET.Analytic.DeckPoly
import InverseGalois.Rigidity.RET.Analytic.DeckPolyMul
import InverseGalois.Rigidity.RET.Analytic.ClearDenom
import InverseGalois.Rigidity.RET.Analytic.ScaledComp
import InverseGalois.Rigidity.RET.Analytic.RationalDeck
import InverseGalois.Rigidity.RET.Analytic.IntegralDeck
import InverseGalois.Rigidity.RET.Analytic.DeckCycles
import InverseGalois.Rigidity.RET.Analytic.Shrink
import InverseGalois.Rigidity.RET.Analytic.DeckClear
import InverseGalois.Rigidity.RET.Analytic.GaloisCycles
import InverseGalois.Rigidity.RET.Analytic.LocalCycles
import InverseGalois.Rigidity.RET.Analytic.Presentation
import InverseGalois.Rigidity.RET.Analytic.GaloisLocalCycles
import InverseGalois.Rigidity.RET.Local.PowerSeriesPlace
import InverseGalois.Rigidity.RET.Local.PuiseuxRoot
import InverseGalois.Rigidity.RET.Local.TaylorSeries
import InverseGalois.Rigidity.RET.Local.TaylorRescale
import InverseGalois.Rigidity.RET.Local.PuiseuxAnalytic
import InverseGalois.Rigidity.RET.Analytic.Pullback
import InverseGalois.Rigidity.RET.Pi1.Topological.PowerBase
import InverseGalois.Rigidity.RET.Pi1.Topological.PowerDisc
import InverseGalois.Rigidity.RET.Pi1.Topological.Lifting
import InverseGalois.Rigidity.RET.Analytic.KummerSection
import InverseGalois.Rigidity.RET.Local.KummerGerm
import InverseGalois.Rigidity.RET.Local.PuiseuxAssembly
import InverseGalois.Rigidity.RET.Local.KummerBranch
import InverseGalois.Rigidity.RET.Analytic.Rotation
import InverseGalois.Rigidity.RET.Local.DiscMonodromy
import InverseGalois.Rigidity.RET.Local.Rescale
import InverseGalois.Rigidity.RET.Analytic.DeckData
import InverseGalois.Rigidity.RET.Local.BranchRotation
import InverseGalois.Rigidity.RET.Local.BranchInertia
import InverseGalois.Rigidity.RET.Analytic.DiscCycle
import InverseGalois.Rigidity.RET.Analytic.DeckElement
import InverseGalois.Rigidity.RET.Local.BranchGeneration
import InverseGalois.Rigidity.RET.Local.BranchElement
import InverseGalois.Rigidity.RET.GeometricBaseChange
import InverseGalois.Rigidity.RET.Local.InertiaGeneration
import InverseGalois.Rigidity.RET.BranchCycleReduce

/-!
# Decomposing the Riemann Existence Theorem: an honest axiom cut

This directory **replaced** the single, over-specified axiom `riemann_existence_ax` (formerly in
`InverseGalois/Rigidity/RiemannExistence.lean`, now deleted) — which handed over the *entire*
`of_regular_family` polynomial bundle in one gulp — with a decomposition that isolates a single,
recognizably textbook Riemann Existence Theorem as the only deep geometric ingredient, and whose
remaining layers are genuine, complete Lean.  The Riemann Existence Theorem is recorded in two forms:
the covers correspondence (`riemann_existence_cover`, `RET.Existence`), which supports the
profinite-`π₁` reformulation (`RET.Pi1.CoverCompletion`, `RET.Pi1.FundamentalGroupCover`); and — the
form consumed by `Rigidity.rigidity_realizable` — the tame-inertia realization
(`inertiaRootData_exists`, `RET.Descent.Tower`), which additionally supplies the branch-cycle inertia
generators and their cyclotomic conjugation, at exactly the interface the branch-cycle descent
consumes.  Everything from that datum down to `IsInverseGalois G` — the descent to `ℚ(T)` and the
Hilbert specialization to `ℚ` — is genuine, complete Lean; the geometric input itself is being built
from the étale/tame fundamental-group theory under `RET.Pi1`.

## Why the old axiom was dishonest

`riemann_existence_ax` asserted, verbatim, the nine-conjunct hypothesis bundle of
`IsInverseGalois.of_regular_family` for `H = φ.range`: a monic `ℚ[T][X]` family `F`, an absolutely
irreducible resolvent `Gp`, cofinite separability, and the *per-specialization* landing (`hland`)
and root (`hroot`) certificates.  A textbook RET produces only a **regular Galois cover** (a field
extension) with prescribed monodromy and branch data; the translation of that cover into an explicit
monic polynomial family *with per-`t` arithmetic certificates* is real algebra that the axiom was
smuggling.  The fully-worked `Aₙ` development (`InverseGalois/Hilbert/Alternating*`) is exactly that
translation done by hand for one family — proof that it is provable, not axiomatic.  This directory
does the same translation *generally* in `RET.Specialization` (`exists_regular_family`), modulo two
isolated arithmetic-geometry bridges.

## The honest cut (chosen architecture)

There are three reasonable places to state RET:

* **Topological** — π₁(ℙ¹(ℂ) ∖ S) and covers ↔ π₁-sets.  *Rejected for now*: Mathlib has covering
  spaces and `FundamentalGroup` but **no concrete π₁ is computed for any space**, no
  covers↔π₁-sets equivalence, no ℂP¹/punctured sphere, no van Kampen; and GAGA / algebraic curves /
  analytification are entirely absent.  This route is a multi-year prerequisite stack.
* **Grothendieck / Galois-category** — the profinite π₁ of the punctured line via
  `CategoryTheory.Galois`.  That framework *does* exist in Mathlib (`GaloisCategory`,
  `IsFundamentalGroup`, `ContAction`), but linking it to actual finite extensions of `ℚ̄(t)` needs
  the covers↔extensions dictionary, which is absent.
* **Algebraic (field-theoretic)** — *chosen*.  State RET directly as: a rigid rational generating
  tuple yields a **regular Galois extension of `ℚ̄(t)`** with the prescribed group and inertia.
  This is textbook (Völklein *Groups as Galois Groups* Thm 2.13; Serre *Topics in Galois Theory*
  §6–8), lives in the algebraic world the repo already inhabits (`ℚ[T][X]`, `specialize`,
  `Polynomial.Gal`), and makes the descent and model-translation layers provable.

## The honest conclusion, and the two Mathlib-blocked steps

The textbook output of the method is a **regular Galois extension of `ℚ(T)`** with group `G` —
not a polynomial bundle.  That conclusion is now named `IsRegularInverseGalois G`
(`RET.Statement`): a finite Galois `L / ℚ(T)` with `Gal ≃* G` in which `ℚ` is relatively
algebraically closed (`algebraicClosure ℚ L = ⊥`).  Against it the honest cut is *two*
recognizable theorems, each a textbook statement, rather than one over-specified bundle:

* **(A) rigidity ⟹ regular realization**: `RigidityCertificate G → IsRegularInverseGalois G`.
  This is Völklein Thm 2.13 = RET + branch-cycle rationality descent.  Mathlib-blocked (GAGA /
  algebraic curves); this is the honest home of the sole geometric axiom.
* **(B) regular realization ⟹ inverse Galois**: `IsRegularInverseGalois G → IsInverseGalois G`.
  This is Hilbert irreducibility / specialization: a regular `ℚ(T)`-extension specializes to a
  `ℚ`-extension with the same group at infinitely many `T`.  The repo already has the
  polynomial-model form of this (`of_regular_family` + `hilbert_irreducibility_theorem`); the
  gap is only the *model translation* abstract-extension → polynomial family (the `Aₙ` template).

Two recognizable theorems is strictly more honest than the current single bundle, which fuses
A, B, and the per-specialization certificates into `of_regular_family`'s hypothesis.

## Layer decomposition

Input: a `RigidityCertificate G` (branch count `r`, rational classes `C`, centerless, a nonempty
rigid set of generating product-one tuples) plus a faithful `φ : G ↪ Sₙ`.
Output: the `of_regular_family` bundle for `H = φ.range`.  In between:

* **L1 — Presentation layer** (`RET.Presentation`).  Pure group theory, all Mathlib vocabulary
  present (`FreeGroup`, `PresentedGroup`).  The sphere group `Γ_r = ⟨x₀,…,x_{r-1} | ∏ xᵢ = 1⟩`; the
  bijection between generating product-one `r`-tuples of `G` and surjections `Γ_r ↠ G`, with
  simultaneous conjugation ↔ post-composition by `Inn G`.  This is the algebraic shadow of
  `π₁(ℙ¹∖S)` and the interface the certificate plugs into.  **Immediately ATP-able.**
* **L2 — Rigidity / branch-cycle descent** `ℚ̄(t) → ℚ(t)`.  The heart of the *method*, and mostly
  provable (Galois-action bookkeeping + group cohomology).  `Gal(ℚ̄/ℚ)` acts on tuples via the
  cyclotomic character on the rational classes; rationality fixes the class-tuple, rigidity (single
  `Inn G`-orbit, from `Rigidity.rigid_card_iff_single_orbit`) makes the cover class Galois-stable,
  and centerless kills the `H¹(·, Z G)` obstruction — giving descent to a *regular* `ℚ(t)`-extension.
* **L3 — RET existence** (the irreducible GAGA content).  A surjection `Γ_r ↠ G` with
  prescribed branch points yields a regular Galois extension of `ℚ̄(t)` with deck group `G` and
  inertia generators in the classes `Cᵢ`.  This is the sole geometric input, and it is being built
  from the étale and topological fundamental-group theory under `RET.Pi1`.  For particular groups it
  is already established outright, with no geometry: for the finite abelian groups by Kummer theory
  (`RET.KummerCover`, `RET.KummerAbelian`), for `Aₙ` and `Sₙ` by Serre's explicit family
  (`RET.SerreCovers`), for the dihedral groups by the substitutions `u ↦ ζ^i·u` and `u ↦ u⁻¹`
  (`RET.DihedralCover`), and for *every* group when there are at most two branch points
  (`RET.ExistenceLowRank`, where the sphere group is cyclic).  `RET.ArtinFixedField` is the general
  engine for such by-hand constructions: a faithful action on a field with invariants `ℚ̄(T)`.
* **L4 — Model translation** to the `of_regular_family` bundle.  Algebra: primitive element +
  resolvent (orbit of a generic linear form) + specialization/reduction-of-inertia.  The `Aₙ`
  development is the worked template.

Assembly (`L5`, **done**): `Rigidity.rigidity_realizable` now composes L1+L2+L3+L4 through the honest
chain `RigidityCertificate G → IsRegularInverseGalois G → IsInverseGalois G`, resting on the single
L3 Riemann Existence Theorem (`inertiaRootData_exists`, in its tame-inertia form) with the L2 descent
and the L4 arithmetic-geometry bridges all genuine Lean.  The over-specified `riemann_existence_ax`
and its file `RiemannExistence.lean` have been deleted.

## Mathlib grounding (survey, 2026-07-29)

READY to consume: `FreeGroup`, `IsFreeGroup`, `PresentedGroup` (+ `toGroup` universal property);
`CategoryTheory.Galois.*` (Galois categories ≌ continuous finite `Aut F`-sets, `IsFundamentalGroup`);
`IsCoveringMap`, path/homotopy lifting, `IsCoveringMap.monodromyFunctor`; `RatFunc`, `FunctionField`
(over `Fq`), `Scheme.functionField`, `IsDominant`; the repo's `ℚ[T][X]`/`specialize`/`Polynomial.Gal`
backbone and the complete `Aₙ` template.

ABSENT (must be built or axiomatized): concrete π₁ of any space; covers↔π₁-sets equivalence /
cover-existence; deck transformations, degree; ℂP¹ / Riemann sphere / punctured sphere as a
space/manifold; Seifert–van Kampen; **GAGA / analytification**; algebraic curves, degree /
ramification of morphisms, covers↔function-field-extensions; Riemann–Roch, genus.  The GAGA + curves
gap is the whole mathematical content of L3, which is therefore stated on its own
(`Rigidity.RET.geomRET`) and never as an axiom; everything else above the cut is elementary by
comparison.

## Currently landed

* **L1** — `InverseGalois.Rigidity.RET.Presentation`: the sphere presentation group `Γ_r`, the
  tuple ↔ surjection dictionary (`sphereHom`, `sphereHom_surjective_iff`), the
  conjugation ↔ inner-automorphism correspondence (`sphereHom_conj`), and the freeness
  `sphereGroup_mulEquiv_free` (`Γ_r ≅ FreeGroup (Fin (r-1))`).  **Complete.**
* **Honest conclusion** — `InverseGalois.Rigidity.RET.Statement`: `IsRegularInverseGalois G`, the
  recognizable target of step (A) and source of step (B) above, with `of_mulEquiv`.
* **Unconditional pieces of L3** — the finite abelian groups (`RET.KummerAbelian`), `Aₙ` and `Sₙ`
  for `n ≥ 3` (`RET.SerreCovers`), the dihedral groups (`RET.DihedralCover`), and every branch datum
  with at most two points
  (`RET.ExistenceLowRank`), together with the closure of the predicate under quotients of the group
  and under isomorphism of the base field (`RET.Pi1.AbsoluteGaloisQuotient`) and Artin's theorem as
  a supplier of covers from invariant theory (`RET.ArtinFixedField`).
* **L3 in full for at most two branch points** — `RET.geomRET_of_le_two`: both directions of the
  covers correspondence, unconditionally, for `r ≤ 2`.  The completeness direction is the harder
  one: a cover of the line branched over at most two points of the sphere has cyclic deck group
  (`RET.LineCover.isCyclic_deck_of_unramifiedOutside_pair`), proved by adjoining a root of the
  coordinate of order the degree of the cover (`RET.KummerPullback`) and moving the two points to
  the origin and infinity by a coordinate change (`RET.TwoPointCyclic`).  For three or more points
  the completeness direction is the GAGA wall itself.
* **The completeness direction for abelian deck groups, at every number of branch points** —
  `RET.exists_branchCycleGenSystem_of_comm`: such a cover embeds in the free abelian cover over the
  same points (`RET.AbelianEmbed`, `RET.FreeAbelianUniversal`), whose standard system of branch
  cycles restricts to the subcover and transports back.  With the existence direction this pins the
  branch loci down exactly: an abelian cover unramified outside `r + 1` points and infinity exists
  iff the group is generated by `r` elements (`RET.exists_cover_iff_exists_generating`).
* **What survives with no hypothesis on the deck group** — `RET.AbelianizedCycles`: a distinguished
  inertia element of a Galois subcover lifts to one of the cover
  (`RET.LineCover.IsInertiaGenAt.exists_lift`), so the branch cycles of the maximal abelian
  subcover lift to distinguished inertia elements over the branch points which generate the deck
  group as a normal subgroup, generate it modulo commutators, and have ordered product a commutator
  (`RET.exists_branchCycles_mod_commutator`); over `r + 1` points the abelianization is generated by
  `r` elements (`RET.exists_generating_abelianization`).  For a nilpotent deck group, generation
  modulo commutators is honest generation, so everything but the product-one relation itself follows
  (`RET.NilpotentCycles`).
* **The branch locus is finite** — `RET.LineCover.exists_unramifiedOutside_finite`: a nontrivial deck
  transformation moves some element of the integral model, and the product of the conjugates of the
  difference is a nonzero polynomial in the coordinate which must vanish wherever the transformation
  is inertial; there are finitely many deck transformations, so finitely many points remain.  The
  branch points therefore no longer have to be prescribed: a cyclic cover of the line unramified at
  infinity simply *has* a system of branch cycles (`RET.exists_branchCycleGenSystem_of_isCyclic'`),
  and the weaker conclusions for nilpotent and arbitrary deck groups likewise stand on their own
  (`RET.BranchLocus`).  The branch locus is then available as an object,
  `RET.LineCover.branchLocus`, and unramifiedness outside a set is containment of it in that set,
  so the low-rank theorems become statements about a cover alone: no branch points means trivial,
  at most two means cyclic (`RET.BranchSet`).
* **The correspondence itself, for abelian deck groups** — `RET.AbelianRET`: the two directions
  above are the two clauses of `RET.GeomRET` with the finite groups replaced by the finite abelian
  ones, so together they are a theorem, `RET.geomRETComm`, of exactly the shape of the wall.  Since
  the branch locus is finite, an abelian cover branched over `r + 1` points has deck group generated
  by `r` elements with nothing prescribed in advance
  (`RET.exists_branchPoints_generating_of_comm`).
* **How many branch points a group needs** — the same count read backwards
  (`RET.two_add_le_card_branchLocus_of_comm`): if the deck group of an abelian cover cannot be
  generated by `r` elements then the cover has at least `r + 2` branch points, since otherwise the
  counting bound would produce a generating tuple that short, padded out by identities.  The
  multi-point Kummer construction realizes a group generated by `r` elements over `r + 1` points, so
  the two bounds meet: an abelian group needs exactly one more branch point than it needs
  generators.  The same lower bound holds for nilpotent deck groups
  (`RET.two_add_le_card_branchLocus_of_isNilpotent`).
* **The groups that occur over a set of points** — `RET.IsDeckGroupOver`: naming the class turns the
  statements above into closure properties of it.  It grows with the set of allowed branch points,
  depends only on the isomorphism type of the group, contains every finite abelian group with a
  product-one generating tuple of the right length, consists of the cyclic groups when at most two
  points are allowed, and is closed under quotients (`RET.IsDeckGroupOver.quotient`) — the fixed
  field of a normal subgroup of the deck group is a Galois subcover realizing the quotient
  (`RET.LineCover.exists_sub_mulEquiv_quotient`), and a subcover branches only where the cover does.
  Branch cycles descend the same way (`RET.LineCover.IsBranchCycleGenSystem.sub`).
* **Unramifiedness at infinity is not a hypothesis** — `RET.LineCover.exists_twist_isUnramifiedAtInfinity`:
  the branch locus is finite and the line is not, so some point is not a branch point; translating it
  to the origin and inverting the coordinate moves it to infinity.  Reading a cover in another
  coordinate does not change its field, so the deck group is untouched, and every group that is a
  deck group at all is a deck group over a finite set of points
  (`RET.exists_finite_isDeckGroupOver`).  Inverting twice returns the cover
  (`RET.LineCover.twistInvInv`), which is what identifies the point at infinity of the inverted
  coordinate with the origin of the original.  The move costs at most one branch point
  (`RET.LineCover.exists_twist_isUnramifiedAtInfinity_ncard`), so the counting survives it: an
  abelian or nilpotent deck group of an arbitrary cover is generated by as many elements as the
  cover has branch points on the affine line (`RET.exists_generating_of_comm_ncard`,
  `RET.exists_generating_of_isNilpotent_ncard`), and correspondingly a cover has at least as many
  branch points as its abelian deck group has generators
  (`RET.succ_le_ncard_branchLocus_of_comm`).  One point is lost against the bound over a
  prescribed branch locus, and must be: ramification at infinity is invisible on the affine line.
  At the bottom of the count this is a characterization
  (`RET.isCyclic_iff_exists_cover_ncard_branchLocus_le_one`): the finite groups occurring with at
  most one branch point on the affine line are exactly the cyclic ones, realized by inverting the
  coordinate of the two-point Kummer cover.  The class of groups occurring with a bounded number of
  affine branch points is `RET.IsAffineDeckGroup`, closed under quotients, trivial at `0`
  (`RET.isAffineDeckGroup_zero_iff`) and the cyclic groups at `1`
  (`RET.isAffineDeckGroup_one_iff`).  For abelian groups the count is settled at every rank
  (`RET.isAffineDeckGroup_iff_exists_generating_of_comm`): a finite abelian group occurs with `n`
  affine branch points exactly when it is generated by `n` elements.  For an arbitrary group only
  the abelianized count survives (`RET.IsAffineDeckGroup.exists_generating_abelianization`), and
  for a nilpotent one that is already the whole count
  (`RET.IsAffineDeckGroup.exists_generating_of_isNilpotent`).  A group presented over a prescribed
  finite branch locus feeds this class (`RET.IsDeckGroupOver.isAffineDeckGroup`) with as many affine
  branch points as the locus has points; the converse fails, and must, since the affine count does
  not see the point at infinity.  Read backwards the abelianized count is a lower bound obstruction
  valid for every group (`RET.not_isAffineDeckGroup_of_abelianization`,
  `RET.le_ncard_branchLocus_of_abelianization`).  Beside quotients the class over a branch locus is
  closed under direct products, at the cost of joining the loci (`RET.IsDeckGroupOver.prod`): two
  covers are placed inside their compositum (`RET.LineCover.compositum`), where they generate and,
  the loci being disjoint, meet in the base field alone, so that the deck group of the compositum
  is the product of the two deck groups (`RET.LineCover.nonempty_deck_mulEquiv_prod`).  Disjointness
  costs nothing, one of the two loci being free to be translated clear of the other
  (`RET.IsDeckGroupOver.translate`, `RET.exists_translate_disjoint`), so that the branch points of a
  product never exceed the two counts together (`RET.IsDeckGroupOver.exists_prod`).  Counted on the
  affine line alone they add exactly (`RET.IsAffineDeckGroup.prod`), nothing being paid for the
  point at infinity, and against the Kummer construction that count is sharp.  A cover of the line
  and a geometric Galois cover being the same thing read two ways
  (`RET.isGeometricGaloisCover_iff_exists_lineCover`), the groups realized by geometric Galois
  covers are therefore closed under finite direct products (`RET.IsGeometricGaloisCover.prod`,
  `RET.isGeometricGaloisCover_pi`).

  Over a fixed branch locus all these covers share one home: the compositum of every cover
  unramified outside `S` and at infinity (`RET.coverField`), an infinite Galois extension of the
  line, directed because two covers are joined inside their compositum
  (`RET.IsCoverFieldOver.sup`) and exhausted by its finite pieces
  (`RET.exists_isCoverFieldOver_of_le`).  Its automorphism group is the geometric fundamental group
  of the punctured line (`RET.geomPi1`), and the groups occurring over `S` are exactly its finite
  quotients by a homomorphism with open kernel
  (`RET.isDeckGroupOver_iff_exists_surjective`): a cover sits inside the compositum and restriction
  of automorphisms to it is such a quotient map (`RET.exists_surjective_of_subextension`), while
  conversely the fixed field of an open normal subgroup is a finite Galois subextension, hence lies
  in a single cover and is cut out by a subcover of it
  (`RET.isDeckGroupOver_of_mulEquiv_subextension`).

  Read through that dictionary, the two low-rank theorems become statements about the fundamental
  group itself, an automorphism of the compositum being determined by its restrictions to the
  finite Galois subextensions (`RET.eq_of_restrictNormalHom`), each of which is again a cover over
  the same points (`RET.isDeckGroupOver_aut`).  With at most one puncture the line is simply
  connected: the compositum is the line itself (`RET.coverField_eq_bot`) and the fundamental group
  is trivial (`RET.subsingleton_geomPi1`).  With at most two it is abelian
  (`RET.commute_geomPi1`), and every finite quotient of it is cyclic
  (`RET.isCyclic_of_surjective_geomPi1`); with exactly two the cyclic groups all occur, by the
  Kummer cover with a generator and its inverse as branch cycles
  (`RET.isDeckGroupOver_of_isCyclic`), so the finite quotients are exactly the finite cyclic groups
  (`RET.exists_surjective_geomPi1_iff_isCyclic`) and the group itself is infinite
  (`RET.infinite_geomPi1`).

  For an arbitrary number of punctures the same dictionary describes the *abelian* quotients
  exactly: over `r + 1` points the finite abelian groups that occur are precisely those generated
  by `r` elements (`RET.isDeckGroupOver_iff_exists_generating_of_comm`), so those are precisely the
  finite abelian quotients of the fundamental group
  (`RET.exists_surjective_geomPi1_iff_exists_generating_of_comm`).  Dropping commutativity, the
  count survives on the abelianization of any finite quotient
  (`RET.exists_generating_abelianization_of_isDeckGroupOver`), which is therefore an obstruction to
  occurring at all (`RET.not_isDeckGroupOver_of_abelianization`).  For a nilpotent group the count
  needs no abelianization at all: generation modulo commutators is generation
  (`RET.exists_generating_of_generating_abelianization`), so a nilpotent group occurring over
  `r + 1` points is itself generated by `r` elements
  (`RET.exists_generating_of_isDeckGroupOver_of_isNilpotent`), and one needing more generators is
  not a finite quotient of the fundamental group
  (`RET.not_exists_surjective_geomPi1_of_isNilpotent`).

  The fundamental groups over different sets of punctures are related by restriction of
  automorphisms: puncturing at more points enlarges the compositum (`RET.coverField_mono`) and gives
  a surjection of fundamental groups (`RET.geomPi1Restrict`, `RET.geomPi1Restrict_surjective`),
  compatible with further enlargements (`RET.geomPi1Restrict_comp`).

  Finally, the branch points of a cover can be located from an equation for it: if the cover is
  generated by roots of monic equations over the coordinate ring, then at every point where all the
  specialized equations stay separable the inertia is trivial
  (`RET.eq_of_mem_inertia_of_separable`, `RET.LineCover.isUnramifiedAt_of_forall_separable`), so the
  branch locus is contained in the degeneracy locus of the equation
  (`RET.LineCover.branchLocus_subset_of_separable`).  That locus is computed by the resultant of the
  equation with its derivative (`RET.degeneracy`, `RET.separable_specialize_iff`): a cover presented
  by an equation whose generic fibre is separable ramifies only over the roots of a nonzero
  polynomial (`RET.degeneracy_ne_zero`, `RET.LineCover.isUnramifiedOutside_degeneracy`).
  Applied to the splitting field of the equation itself (`RET.eqCover`), whose roots generate it,
  this makes the branch-point counting arithmetic: the Galois group of a monic separable equation
  over `ℚ̄(T)` occurs with at most `deg` of the degeneracy polynomial many branch points on the
  affine line (`RET.isAffineDeckGroup_gal`), so its abelianization is generated by that many
  elements (`RET.exists_generating_abelianization_gal`) and a degeneracy polynomial of degree at
  most one forces a cyclic group (`RET.isCyclic_gal_of_natDegree_degeneracy_le_one`).

  Underneath all of this sits the field of constants.  A rational function algebraic over the
  constants is a constant (`RET.algebraicClosure_ratFunc_eq_bot`), so `K(T) / K` is itself regular;
  and having no constants beyond `ℚ` passes to any subfield
  (`RET.algebraicClosure_eq_bot_of_ringHom`), because over `ℚ` every ring homomorphism is a
  `ℚ`-algebra homomorphism.  Consequently the target class of the geometric half is closed under
  passing to quotients: the fixed field of a normal subgroup is Galois over `ℚ(T)` with the quotient
  group, and it acquires no constants beyond those of the big extension, so a quotient of a regular
  inverse Galois group is again one (`IsRegularInverseGalois.of_surjective`,
  `IsRegularInverseGalois.quotient`).

  Regularity is moreover the *same* condition as absolute irreducibility, not merely implied by it.
  In the base change `ℚ̄(T) ⊗ L`, an element of `L` algebraic over the constants satisfies a
  polynomial that splits, so it agrees with one root; the normalized trace of `L / ℚ(T)` pushes that
  root into `ℚ(T)`, where regularity of the base makes it a constant
  (`RET.algebraicClosure_eq_bot_of_isField_tensor`).  Since every polynomial over `ℚ` splits in
  `ℚ̄(T)` (`RET.splits_map_toClosureFrac_comp_C`), a finite extension of `ℚ(T)` generated by a root
  of `F ∈ ℚ[T][X]` is regular exactly when `F` stays irreducible over `ℚ̄(T)`
  (`RET.algebraicClosure_eq_bot_iff_irreducible_map_toClosureFrac`) — the absolute irreducibility
  that every construction here already checks in order to run Hilbert irreducibility.

  That criterion turns a polynomial into a regular realization: a finite Galois extension of `ℚ(T)`
  generated by a root of an absolutely irreducible `F ∈ ℚ[T][X]`, together with an identification of
  its Galois group, is exactly the data of `IsRegularInverseGalois`
  (`IsRegularInverseGalois.of_primitive_irreducible`); the rational structure the definition asks
  for is the canonical one every field of characteristic zero carries, once one checks by hand that
  the localization's scalar action on `ℚ(T)` is multiplication by a rational number
  (`RET.rat_smul_ratFunc`).  The smallest instance needs no geometric input at all: `X² - T` is
  Eisenstein at `T` over any coefficient field, so `ℚ(T)(√T)` is a regular quadratic extension and
  every group of order two is a regular inverse Galois group
  (`RET.isRegularInverseGalois_of_card_eq_two`) — and hence, through the specialization theorem, a
  Galois group over `ℚ` (`RET.isInverseGalois_of_card_eq_two`).

  Order three is out of reach of radicals — `ℚ(T)` has no cube root of unity — but not out of
  reach of an explicit polynomial: Shanks' simplest cubic `X³ - T X² - (T+3) X - 1` has the three
  roots `β`, `-(β+1)⁻¹`, `-(β+1)/β`, an orbit of the order-three Möbius transformation
  `z ↦ -1/(z+1)`, so one root already generates a splitting field.  It is linear in `T` with
  coprime coefficients, hence irreducible over `k(T)` for every coefficient field `k` at once
  (`RET.irreducible_shanksBase_map`), which is both the irreducibility and the regularity input.
  Every group of order three is therefore a regular inverse Galois group
  (`RET.isRegularInverseGalois_of_card_eq_three`), and a Galois group over `ℚ`
  (`RET.isInverseGalois_of_card_eq_three`).

  Beyond the cyclic groups the polynomials give out, and the systematic supplier takes over: a
  finite group of automorphisms of `ℚ(T)` fixing the constants is, by Artin's theorem, the Galois
  group of `ℚ(T)` over its fixed field, and by Lüroth's theorem that fixed field is *again* a field
  of rational functions, since it is an intermediate field of `ℚ(T)/ℚ` other than `ℚ` itself.  So
  the group is realized over a base isomorphic to `ℚ(T)`, and the extension has no constants beyond
  `ℚ`: any finite group acting faithfully on `ℚ(T)` is a regular inverse Galois group
  (`IsRegularInverseGalois.of_faithful_smul`, or `IsRegularInverseGalois.of_injective_ringAut` for
  a group presented as an injective family of ring automorphisms).  The supply of such actions is
  the Möbius group: `u ↦ (a u + b)/(c u + d)` is an automorphism of `ℚ(u)` whenever `a d - b c ≠ 0`
  (`RET.mobiusAut`), substitution composes these by matrix multiplication (`RET.mobiusAut_mul`),
  and two of them agree exactly when their matrices are proportional (`RET.mobiusAut_ne`), so every
  relation among them is a matrix identity.

  The first non-cyclic group this reaches is the symmetric group on three letters, acting as the
  anharmonic group of the six substitutions permuting `{0, 1, ∞}`.  Its rotation `u ↦ 1/(1 - u)`
  has order three, its reflection `u ↦ 1/u` is an involution inverting the rotation, and a rotation
  with an inverting involution is precisely a dihedral group (`RET.dihedralLift`, injective by
  `RET.dihedralLift_injective` once the rotation has the right order and the involution is none of
  its powers).  So the symmetric group on three letters is a regular inverse Galois group
  (`RET.isRegularInverseGalois_perm_fin_three`), and a Galois group over `ℚ`
  (`RET.isInverseGalois_perm_fin_three`).

  The same two ingredients — a rotation of the right order and an involution inverting it — are
  available for the other dihedral groups whose rotation is realizable over the rationals, and the
  criterion `RET.isRegularInverseGalois_dihedralGroup` packages them.  What has to be exhibited is a
  matrix of finite order in the projective group: `u ↦ -u` has order two, `u ↦ (u - 1)/(u + 1)` has
  order four since its square is `u ↦ -1/u`, and `u ↦ (2u - 1)/(u + 1)` has order six, its square
  and its cube being visibly of order three and two.  Each is inverted by a reflection, and every
  relation needed is a proportionality of two-by-two matrices, checked entrywise
  (`RET.mobiusRingAut_mul_eq`, `RET.mobiusRingAut_ne`).  The Klein four-group and the dihedral
  groups of order eight and of order twelve are therefore regular inverse Galois groups
  (`RET.isRegularInverseGalois_dihedralGroup_two`, `_four`, `_six`), and Galois groups over `ℚ`
  (`RET.isInverseGalois_dihedralGroup_two`, `_four`, `_six`).

  Dropping the involution and keeping the rotation gives the cyclic groups by the same route: the
  powers of a substitution of finite order are already a finite group of automorphisms of `ℚ(u)`
  (`RET.isRegularInverseGalois_zpowers`), and any cyclic group of that order is a copy of them
  (`RET.isRegularInverseGalois_of_isCyclic`).  So the rotations of orders two, four and six settle
  the cyclic groups of those orders, and with the quadratic and the cubic already in hand every
  cyclic group of order `1`, `2`, `3`, `4` or `6` is a regular inverse Galois group
  (`RET.isRegularInverseGalois_of_isCyclic_card_mem`).  Those orders and the five dihedral groups
  of order `2`, `4`, `6`, `8` and `12` (`RET.isRegularInverseGalois_dihedralGroup_mem`) exhaust the
  finite subgroups of the projective linear group over the rationals, so the whole list is realized
  regularly (`RET.isRegularInverseGalois_of_isMobius`) and over `ℚ`
  (`RET.isInverseGalois_of_isMobius`).

  Beyond the substitutions there is a second, wholly different supply of regular realizations: a
  Galois extension of `ℚ(T)` presented by a *resolvent*.  The Hilbert-irreducibility side of this
  development consumes a family over `ℚ[T]` together with an absolutely irreducible resolvent of
  degree `|G|` and specializes it; read over `ℚ(T)` instead, the same two ingredients — an
  injection of the Galois group into `G` and a root of the resolvent — already suffice, and the
  regularity comes for free (`IsRegularInverseGalois.of_embeds_and_root`).  Three inequalities
  close the loop: the injection bounds the Galois group by `|G|`, the root generates a subfield of
  degree `|G|` because the resolvent is its minimal polynomial, and a subfield is no larger than
  the field.  So all three are equalities, the root is a primitive element, and the absolute
  irreducibility of the resolvent — which forced it to be the minimal polynomial in the first
  place — is exactly the statement that the extension acquires no new constants.

  Feeding that criterion the resolvent already built for the Morse family `Xⁿ − X − T` realizes
  the symmetric groups.  Both of its inputs come free over the generic point: the defining
  property of a generic linear resolvent is a descent identity valid in *every* field where the
  family splits, so over the splitting field of the family over `ℚ(T)` the resolvent becomes the
  product of the linear forms attached to the permutations of the roots, each of them a root of it
  (`RET.generic_resolvent_root`); and the landing certificate is just the faithful action of the
  Galois group on the `n` roots (`RET.exists_injective_galActionHom`).  So the symmetric group on
  `n` letters is a regular inverse Galois group for every `n`
  (`RET.isRegularInverseGalois_perm_fin`), and a Galois group over `ℚ`
  (`RET.isInverseGalois_perm_fin`).

  The alternating groups follow the same route through Serre's square-discriminant families, the
  substituted family for even `n` and the conic family for odd `n`.  Every ingredient they were
  given for the specialization argument was already stated for an arbitrary evaluation of the
  coefficient ring into a field where the family splits, so every one of them can be read at the
  generic point instead of at a rational parameter: the discriminant is the square of an explicit
  polynomial there (`AlternatingFamily.serreAnDeltaPoly_sq`), which is the landing certificate
  `Gal ↪ Aₙ`; the orbit resolvent becomes the product of the linear forms attached to the *even*
  permutations of the roots, and the form attached to the identity is a root of it
  (`RET.generic_alt_resolvent_root`); and the geometric monodromy computation already says the
  resolvent is absolutely irreducible.  Assembled (`RET.isRegularInverseGalois_alternating_of_family`)
  this realizes the alternating group on `n` letters regularly for every `n`
  (`RET.isRegularInverseGalois_alternatingGroup`), and over `ℚ`
  (`RET.isInverseGalois_alternatingGroup`).

  Finally, the catalogue of regular realizations is closed under direct products of coprime order
  (`IsRegularInverseGalois.prod_of_coprime`).  The group theory is the one already used over `ℚ`:
  embed the two realizing extensions into an algebraic closure of `ℚ(T)` and restrict to the two
  factors of the compositum (`galSupProdEquiv`).  What is new over `ℚ(T)` is that the compositum
  must be shown to be regular again — and it need not be, since `ℚ(T)(√T)` and `ℚ(T)(√(-T))` are
  regular but their compositum contains a square root of `-1`.  Coprimality is what excludes this:
  over a regular field a rational minimal polynomial stays irreducible
  (`RET.natDegree_minpoly_dvd_finrank`), so a constant of the compositum has one degree over `ℚ`
  which divides both steps of the tower, and those two steps are the degrees of the two factors
  (`RET.algebraicClosure_sup_eq_bot`).
-/
