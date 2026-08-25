import InverseGalois.CFT.Approximation.Basic
import InverseGalois.CFT.Approximation.Completion
import InverseGalois.CFT.Approximation.Places
import InverseGalois.CFT.Approximation.PowClass
import InverseGalois.CFT.Brauer.BaseChange
import InverseGalois.CFT.Brauer.Centralizer
import InverseGalois.CFT.Brauer.CentralizerProduct
import InverseGalois.CFT.Brauer.CrossedProduct
import InverseGalois.CFT.Brauer.CrossedProductCohomologous
import InverseGalois.CFT.Brauer.CrossedProductMul
import InverseGalois.CFT.Brauer.CrossedProductRecognition
import InverseGalois.CFT.Brauer.CrossedProductSimple
import InverseGalois.CFT.Brauer.CrossedProductSplit
import InverseGalois.CFT.Brauer.CrossedProductSplitting
import InverseGalois.CFT.Brauer.CyclicAlgebra
import InverseGalois.CFT.Brauer.CyclicBrauer
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Brauer.Division
import InverseGalois.CFT.Brauer.Exponent
import InverseGalois.CFT.Brauer.GaloisSplitting
import InverseGalois.CFT.Brauer.Group
import InverseGalois.CFT.Brauer.H2Brauer
import InverseGalois.CFT.Brauer.H2Surjective
import InverseGalois.CFT.Brauer.Kernel
import InverseGalois.CFT.Brauer.MaximalSubfield
import InverseGalois.CFT.Brauer.Opposite
import InverseGalois.CFT.Brauer.Primary
import InverseGalois.CFT.Brauer.QuadraticExt
import InverseGalois.CFT.Brauer.Quaternion
import InverseGalois.CFT.Brauer.RationalBrauer
import InverseGalois.CFT.Brauer.RealBrauer
import InverseGalois.CFT.Brauer.RealPlace
import InverseGalois.CFT.Brauer.Semilinear
import InverseGalois.CFT.Brauer.SkolemNoether
import InverseGalois.CFT.Brauer.Split
import InverseGalois.CFT.Brauer.SplittingSubfield
import InverseGalois.CFT.Brauer.TensorSimple
import InverseGalois.CFT.Brauer.Tower
import InverseGalois.CFT.Compositum
import InverseGalois.CFT.Cyclotomic.BuildingBlock
import InverseGalois.CFT.Cyclotomic.Chebotarev
import InverseGalois.CFT.Cyclotomic.CyclicSubfield
import InverseGalois.CFT.Cyclotomic.CyclotomicInertiaDeg
import InverseGalois.CFT.Cyclotomic.DivisorSubfield
import InverseGalois.CFT.Cyclotomic.Frobenius
import InverseGalois.CFT.Cyclotomic.FrobeniusSplitting
import InverseGalois.CFT.Cyclotomic.InertiaOrder
import InverseGalois.CFT.Cyclotomic.OnePrimeRamified
import InverseGalois.CFT.Cyclotomic.PrimeSelection
import InverseGalois.CFT.Cyclotomic.Ramified
import InverseGalois.CFT.Cyclotomic.Splitting
import InverseGalois.CFT.Cyclotomic.SquareRoots
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Decomposition
import InverseGalois.CFT.Disjoint
import InverseGalois.CFT.GaloisDescent
import InverseGalois.CFT.GroupCohomology.Classification
import InverseGalois.CFT.GroupCohomology.CentralLift
import InverseGalois.CFT.GroupCohomology.Cohomologous
import InverseGalois.CFT.GroupCohomology.CoprimeCoboundary
import InverseGalois.CFT.GroupCohomology.CoprimeSplit
import InverseGalois.CFT.GroupCohomology.Corestriction
import InverseGalois.CFT.GroupCohomology.Cyclic
import InverseGalois.CFT.GroupCohomology.CyclicH1
import InverseGalois.CFT.GroupCohomology.CyclicCoboundary
import InverseGalois.CFT.GroupCohomology.CyclicH2
import InverseGalois.CFT.GroupCohomology.CyclicSurjective
import InverseGalois.CFT.GroupCohomology.H1Transport
import InverseGalois.CFT.GroupCohomology.MapCoboundary
import InverseGalois.CFT.GroupCohomology.OfCocycle
import InverseGalois.CFT.GroupCohomology.SylowRes
import InverseGalois.CFT.GroupCohomology.ToCocycle
import InverseGalois.CFT.Global.DavenportCassels
import InverseGalois.CFT.Global.DescentTools
import InverseGalois.CFT.Global.Existence
import InverseGalois.CFT.Global.ExistenceGeneral
import InverseGalois.CFT.Global.HasseMinkowski
import InverseGalois.CFT.Global.HasseNorm
import InverseGalois.CFT.Global.HilbertBimul
import InverseGalois.CFT.Global.HilbertMulPlaces
import InverseGalois.CFT.Global.HilbertPlaces
import InverseGalois.CFT.Global.HilbertProduct
import InverseGalois.CFT.Global.JacobiNonresidue
import InverseGalois.CFT.Global.LocalSquare
import InverseGalois.CFT.Global.LocalSquares
import InverseGalois.CFT.Global.OddGenerators
import InverseGalois.CFT.Global.OddValuation
import InverseGalois.CFT.Global.DiagBase
import InverseGalois.CFT.Global.DiagForm
import InverseGalois.CFT.Global.DiagHasse
import InverseGalois.CFT.Global.DiagRepr
import InverseGalois.CFT.Global.DiagScale
import InverseGalois.CFT.Global.DiagSplit
import InverseGalois.CFT.Global.IntApprox
import InverseGalois.CFT.Global.MatHasse
import InverseGalois.CFT.Global.Meyer
import InverseGalois.CFT.Global.OddQuinary
import InverseGalois.CFT.Global.OddUnitIsotropy
import InverseGalois.CFT.Global.QuaternaryForms
import InverseGalois.CFT.Global.QuinaryForms
import InverseGalois.CFT.Global.RealSigns
import InverseGalois.CFT.Global.RationalSquareClasses
import InverseGalois.CFT.Global.Reciprocity
import InverseGalois.CFT.Global.SevenModEight
import InverseGalois.CFT.Global.SquareClassApprox
import InverseGalois.CFT.Global.SquarefreeCRT
import InverseGalois.CFT.Global.TernaryForms
import InverseGalois.CFT.Global.ThreeSquares
import InverseGalois.CFT.Global.ThreeSquaresOdd
import InverseGalois.CFT.Global.ThreeSquaresTwo
import InverseGalois.CFT.Global.TwoGenerators
import InverseGalois.CFT.Herbrand
import InverseGalois.CFT.InertiaAbelian
import InverseGalois.CFT.InertiaGeneration
import InverseGalois.CFT.InertiaRestrict
import InverseGalois.CFT.InertiaSubgroup
import InverseGalois.CFT.KroneckerWeber
import InverseGalois.CFT.Kummer.CyclicIndex
import InverseGalois.CFT.Kummer.CyclotomicDescent
import InverseGalois.CFT.Kummer.Denominator
import InverseGalois.CFT.Kummer.GlobalPower
import InverseGalois.CFT.Kummer.InflationRootsOfUnity
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.Kummer.LocalSurjective
import InverseGalois.CFT.Kummer.Pairing
import InverseGalois.CFT.Kummer.PowBasis
import InverseGalois.CFT.Kummer.PowIndex
import InverseGalois.CFT.Kummer.PowerCriterion
import InverseGalois.CFT.Kummer.RadicalClosure
import InverseGalois.CFT.Kummer.RootIndex
import InverseGalois.CFT.Kummer.RootsInBase
import InverseGalois.CFT.Kummer.SUnitExt
import InverseGalois.CFT.Kummer.SUnitUnramified
import InverseGalois.CFT.Kummer.SecondInequality
import InverseGalois.CFT.Kummer.Unramified
import InverseGalois.CFT.Level
import InverseGalois.CFT.Local.AdicAction
import InverseGalois.CFT.Local.AdicFamily
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Local.AdicPowIndex
import InverseGalois.CFT.Local.AdicResidue
import InverseGalois.CFT.Local.AdicUnits
import InverseGalois.CFT.Local.AdicUnramified
import InverseGalois.CFT.Local.ComplexHerbrand
import InverseGalois.CFT.Local.DyadicAnisotropic
import InverseGalois.CFT.Local.DyadicHilbert
import InverseGalois.CFT.Local.DyadicHilbertMul
import InverseGalois.CFT.Local.DyadicNondegenerate
import InverseGalois.CFT.Local.DyadicQuaternary
import InverseGalois.CFT.Local.DyadicNormFive
import InverseGalois.CFT.Local.DyadicQuinary
import InverseGalois.CFT.Local.Exp
import InverseGalois.CFT.Local.ExpAction
import InverseGalois.CFT.Local.ExpEquiv
import InverseGalois.CFT.Local.ExpSurjective
import InverseGalois.CFT.Local.FiltrationAction
import InverseGalois.CFT.Local.FiltrationFinite
import InverseGalois.CFT.Local.FiltrationHerbrand
import InverseGalois.CFT.Local.GradedFinite
import InverseGalois.CFT.Local.HilbertIdentities
import InverseGalois.CFT.Local.HilbertMap
import InverseGalois.CFT.Local.HilbertMul
import InverseGalois.CFT.Local.HilbertSymbol
import InverseGalois.CFT.Local.InfiniteAction
import InverseGalois.CFT.Local.InfiniteFamily
import InverseGalois.CFT.Local.InfiniteHerbrand
import InverseGalois.CFT.Local.InfiniteNormIndex
import InverseGalois.CFT.Local.InfinitePowIndex
import InverseGalois.CFT.Local.LegendreHilbert
import InverseGalois.CFT.Local.NormIndex
import InverseGalois.CFT.Local.NormalLattice
import InverseGalois.CFT.Local.OddAnisotropic
import InverseGalois.CFT.Local.PadicHilbert
import InverseGalois.CFT.Local.PadicHilbertMul
import InverseGalois.CFT.Local.PadicLocalField
import InverseGalois.CFT.Local.PadicSquares
import InverseGalois.CFT.Local.NatValuation
import InverseGalois.CFT.Local.PadicSquaresTwo
import InverseGalois.CFT.Local.PowClose
import InverseGalois.CFT.Local.PowNeighbourhood
import InverseGalois.CFT.Local.RamifiedNormForm
import InverseGalois.CFT.Local.TraceIntegral
import InverseGalois.CFT.Local.TrivialIndex
import InverseGalois.CFT.Local.UnitFiltration
import InverseGalois.CFT.Local.UnitHerbrandChain
import InverseGalois.CFT.Local.UnitIndex
import InverseGalois.CFT.Local.UnitPowIndex
import InverseGalois.CFT.Local.UnitValuation
import InverseGalois.CFT.Local.UnramifiedCoboundary
import InverseGalois.CFT.Local.UnramifiedNormForm
import InverseGalois.CFT.Local.UnramifiedUnits
import InverseGalois.CFT.Local.ValuedTopology
import InverseGalois.CFT.NormSubgroup
import InverseGalois.CFT.PiIndex
import InverseGalois.CFT.ScalarSemidirect
import InverseGalois.CFT.Scholz.Condition
import InverseGalois.CFT.Scholz.FrattiniStep
import InverseGalois.CFT.Scholz.Induction
import InverseGalois.CFT.Scholz.NilpotentOdd
import InverseGalois.CFT.Scholz.NilpotentSylowTwo
import InverseGalois.CFT.Scholz.PrimeChoice
import InverseGalois.CFT.Scholz.RadicalDisjoint
import InverseGalois.CFT.Scholz.RadicalTower
import InverseGalois.CFT.Scholz.Realization
import InverseGalois.CFT.Scholz.Selector
import InverseGalois.CFT.Scholz.SplitCase
import InverseGalois.CFT.Scholz.SplitReduction
import InverseGalois.CFT.Scholz.SplitStep
import InverseGalois.CFT.Scholz.Tame
import InverseGalois.CFT.SplitCompositum
import InverseGalois.CFT.SquareClasses
import InverseGalois.CFT.SubgroupCounting
import InverseGalois.CFT.SubgroupIndex
import InverseGalois.CFT.TameCharacter
import InverseGalois.CFT.TameRamification
import InverseGalois.CFT.Tate.Augmentation
import InverseGalois.CFT.Tate.Averaging
import InverseGalois.CFT.Tate.Basic
import InverseGalois.CFT.Tate.BrauerRelative
import InverseGalois.CFT.Tate.Commensurable
import InverseGalois.CFT.Tate.Congr
import InverseGalois.CFT.Tate.CyclicAction
import InverseGalois.CFT.Tate.CyclicHilbert90
import InverseGalois.CFT.Tate.CyclicInduced
import InverseGalois.CFT.Tate.Exact
import InverseGalois.CFT.Tate.Family
import InverseGalois.CFT.Tate.FamilyCoboundary
import InverseGalois.CFT.Tate.FamilyFree
import InverseGalois.CFT.Tate.FamilyNorm
import InverseGalois.CFT.Tate.FamilyOrbit
import InverseGalois.CFT.Tate.FamilyOrbits
import InverseGalois.CFT.Tate.FamilyReindex
import InverseGalois.CFT.Tate.FamilyRestrict
import InverseGalois.CFT.Tate.FamilyRestrictOrbit
import InverseGalois.CFT.Tate.FamilyRing
import InverseGalois.CFT.Tate.FamilySigma
import InverseGalois.CFT.Tate.Fibers
import InverseGalois.CFT.Tate.Finite
import InverseGalois.CFT.Tate.FiniteExact
import InverseGalois.CFT.Tate.Galois
import InverseGalois.CFT.Tate.GaloisH0
import InverseGalois.CFT.Tate.H0Norm
import InverseGalois.CFT.Tate.Herbrand
import InverseGalois.CFT.Tate.Hexagon
import InverseGalois.CFT.Tate.InducedLattice
import InverseGalois.CFT.Tate.InfinitePlaces
import InverseGalois.CFT.Tate.Isogeny
import InverseGalois.CFT.Tate.Lattice
import InverseGalois.CFT.Tate.Mul
import InverseGalois.CFT.Tate.NormSurjective
import InverseGalois.CFT.Tate.NormalBasis
import InverseGalois.CFT.Tate.Orbit
import InverseGalois.CFT.Tate.OrbitCocycle
import InverseGalois.CFT.Tate.OrbitIndex
import InverseGalois.CFT.Tate.OrbitInduced
import InverseGalois.CFT.Tate.OrbitRange
import InverseGalois.CFT.Tate.OrbitTwist
import InverseGalois.CFT.Tate.PermLattice
import InverseGalois.CFT.Tate.Permutation
import InverseGalois.CFT.Tate.Pi
import InverseGalois.CFT.Tate.PiSplit
import InverseGalois.CFT.Tate.Primes
import InverseGalois.CFT.Tate.Prod
import InverseGalois.CFT.Tate.QuotientFixed
import InverseGalois.CFT.Tate.RealBasis
import InverseGalois.CFT.Tate.RealForm
import InverseGalois.CFT.Tate.RealHerbrand
import InverseGalois.CFT.Tate.Restrict
import InverseGalois.CFT.Tate.Shapiro
import InverseGalois.CFT.Tate.Surjection
import InverseGalois.CFT.Tate.Trivial
import InverseGalois.CFT.Tate.TrivialLattice
import InverseGalois.CFT.Units.ABHN
import InverseGalois.CFT.Units.ABHNTorsion
import InverseGalois.CFT.Units.AdicFixed
import InverseGalois.CFT.Units.AdicIdeleHerbrand
import InverseGalois.CFT.Units.AdicOrbit
import InverseGalois.CFT.Units.AdicSIdeles
import InverseGalois.CFT.Units.ArchimedeanIdeles
import InverseGalois.CFT.Units.BaseChangeIndex
import InverseGalois.CFT.Units.ClassSet
import InverseGalois.CFT.Units.CompletionFinite
import InverseGalois.CFT.Units.CompletionGalois
import InverseGalois.CFT.Units.CompletionUnits
import InverseGalois.CFT.Units.CyclicTrivial
import InverseGalois.CFT.Units.Decomposition
import InverseGalois.CFT.Units.DecompositionOutside
import InverseGalois.CFT.Units.EquivariantLabel
import InverseGalois.CFT.Units.FirstInequality
import InverseGalois.CFT.Units.FrobeniusPlace
import InverseGalois.CFT.Units.GaloisAction
import InverseGalois.CFT.Units.GeneratingPrimes
import InverseGalois.CFT.Units.HasseNorm
import InverseGalois.CFT.Units.Herbrand
import InverseGalois.CFT.Units.Idele
import InverseGalois.CFT.Units.IdeleClass
import InverseGalois.CFT.Units.IdeleClassComap
import InverseGalois.CFT.Units.IdeleClassFixed
import InverseGalois.CFT.Units.IdeleClassH1
import InverseGalois.CFT.Units.IdeleClassH1Full
import InverseGalois.CFT.Units.IdeleClassIndex
import InverseGalois.CFT.Units.IdeleClassSES
import InverseGalois.CFT.Units.IdeleClassTower
import InverseGalois.CFT.Units.IdeleCoboundary
import InverseGalois.CFT.Units.IdeleFixed
import InverseGalois.CFT.Units.IdeleNorm
import InverseGalois.CFT.Units.IdeleNormTower
import InverseGalois.CFT.Units.IdeleRep
import InverseGalois.CFT.Units.IdeleRestrict
import InverseGalois.CFT.Units.IdeleTower
import InverseGalois.CFT.Units.InfiniteComap
import InverseGalois.CFT.Units.InfiniteFixed
import InverseGalois.CFT.Units.InfiniteGalois
import InverseGalois.CFT.Units.InfiniteIdele
import InverseGalois.CFT.Units.InfiniteOrbit
import InverseGalois.CFT.Units.LocalEmbedding
import InverseGalois.CFT.Units.LocalIdele
import InverseGalois.CFT.Units.LocalNorm
import InverseGalois.CFT.Units.LocalPowIdele
import InverseGalois.CFT.Units.NormIndex
import InverseGalois.CFT.Units.OrbitPlaces
import InverseGalois.CFT.Units.PlaceComap
import InverseGalois.CFT.Units.PlaceRestrict
import InverseGalois.CFT.Units.PlaceTower
import InverseGalois.CFT.Units.Places
import InverseGalois.CFT.Units.PowIdele
import InverseGalois.CFT.Units.PowSIdeleClass
import InverseGalois.CFT.Units.PowSIdeleNorm
import InverseGalois.CFT.Units.PrimeAbove
import InverseGalois.CFT.Units.SIdeleClass
import InverseGalois.CFT.Units.SIdeleHerbrand
import InverseGalois.CFT.Units.SIdeleNorm
import InverseGalois.CFT.Units.SUnit
import InverseGalois.CFT.Units.SUnitHerbrand
import InverseGalois.CFT.Units.SUnitIndex
import InverseGalois.CFT.Units.SUnitValuation
import InverseGalois.CFT.Units.SolvableNorm
import InverseGalois.CFT.Units.SplitNorm
import InverseGalois.CFT.Units.SplitOutside
import InverseGalois.CFT.Units.SplitPlaces
import InverseGalois.CFT.Units.SplitPowIdele
import InverseGalois.CFT.Units.SplitPowNorm
import InverseGalois.CFT.Units.UnitLattice
import InverseGalois.CFT.Unramified
import InverseGalois.CFT.UnramifiedCompositum

/-!
# Towards class field theory

The arithmetic input that Scholz–Reichardt and Shafarevich need beyond what
`InverseGalois.NumberTheory` supplies is class field theory. This directory collects the pieces of
it that are available here.

## Ramification over the rationals

* `InverseGalois.CFT.Unramified` proves Minkowski's theorem that `ℚ` has no extension unramified at
  every finite prime.
* `InverseGalois.CFT.Cyclotomic.Ramified` shows that a cyclotomic field of conductor `n`, and every
  subfield of one, is unramified at every prime not dividing `n`.
* `InverseGalois.CFT.Level` records that the ramified primes of a number field are ramified in
  every field above it, and defines the level condition that organises the Scholz–Reichardt
  induction.
* `InverseGalois.CFT.Decomposition` gives the decomposition and inertia groups of a prime of a
  Galois number field: inertia is trivial exactly at an unramified prime, where the decomposition
  group is generated by the Frobenius.
* `InverseGalois.CFT.Disjoint` shows that number fields with disjoint ramification meet in `ℚ`.
* `InverseGalois.CFT.InertiaSubgroup` identifies the inertia subgroup of a prime with the subgroup
  fixing the prime pointwise once the residue degree is one, and with the whole decomposition group
  once the ramification index is the degree, and follows inertia along the Galois action.
* `InverseGalois.CFT.Compositum` computes the Galois group of a compositum of two Galois
  extensions meeting in the base as the product of their Galois groups.
* `InverseGalois.CFT.UnramifiedCompositum` computes the ramification of a compositum: a prime
  ramifies in `A ⊔ B` exactly when it ramifies in `A` or in `B`, with no disjointness hypothesis,
  so the level condition passes to a compositum.
* `InverseGalois.CFT.SplitCompositum` does the same for residue degrees, which do not behave so
  simply: the order of a decomposition group is the ramification index times the residue degree,
  and restriction embeds the decomposition group of a compositum into that of one factor as soon
  as the prime splits completely in the other, so residue degree one is inherited.

## Towards Kronecker–Weber

* `InverseGalois.CFT.SubgroupCounting` bounds the order of a group generated by finitely many
  normal subgroups by the product of their orders.
* `InverseGalois.CFT.InertiaGeneration` proves that the inertia subgroups of the maximal ideals of
  a Galois number field generate its whole Galois group, the group-theoretic form of Minkowski's
  theorem, and records how inertia transforms under the Galois action and under passage to a
  subgroup.
* `InverseGalois.CFT.InertiaAbelian` combines the two: in an abelian extension all the primes above
  a rational prime share an inertia subgroup, so the degree of the field is bounded by the product
  of the ramification indices of the ramified rational primes.
* `InverseGalois.CFT.InertiaRestrict` restricts inertia to a subfield, and deduces that a prime
  dividing the order of inertia in a compositum already divides it in one of the two factors.
* `InverseGalois.CFT.ScalarSemidirect` proves Serre's disjointness lemma in group-theoretic form:
  the semidirect product of `(ℤ/ℓ)ˢ` by the scalar action of `(ℤ/ℓ)ˣ` has abelianization of order
  `ℓ - 1`, hence no quotient of order `ℓ` when `ℓ` is odd.
* `InverseGalois.CFT.TameRamification` isolates the tamely ramified extensions, those in which no
  residue characteristic divides a ramification index, and shows that the class is closed under
  compositum and contains the cyclotomic fields of squarefree conductor.
* `InverseGalois.CFT.CyclotomicCompositum` places a number field and a cyclotomic field side by
  side inside an algebraic closure of `ℚ` and compares the degree of their compositum with
  `φ n`, which is what turns a degree bound into an embedding into a cyclotomic field.
* `InverseGalois.CFT.Cyclotomic.InertiaOrder` computes the order of inertia at a rational prime
  `p` in `ℚ(ζₙ)` as `φ (p ^ k)`, `p ^ k` the exact power of `p` dividing `n`, and multiplies these
  local orders back up to the global degree `φ n`.
* `InverseGalois.CFT.TameCharacter` builds the tame character of an inertia subgroup, the
  homomorphism to the units of the residue field sending an element to the class of `σ π / π` for
  a uniformizer `π`.  It is injective once the residue characteristic does not divide the order of
  inertia, and equivariant for the Frobenius, so in an abelian extension the order of inertia
  divides `p - 1`.
* `InverseGalois.CFT.KroneckerWeber` assembles all of this into the **Kronecker–Weber theorem for
  tamely ramified abelian number fields**: such a field embeds into the cyclotomic field whose
  conductor is the product of the ramified primes.
* `InverseGalois.CFT.Cyclotomic.SquareRoots` covers the wildly ramified quadratic case by hand:
  a primitive eighth root of unity supplies square roots of `-1` and of `2`, a quadratic Gauss sum
  supplies a square root of every odd prime, so every rational is a square in a cyclotomic field
  and **every quadratic number field embeds into one**.

## Reciprocity for the rational field

* `InverseGalois.CFT.Cyclotomic.Frobenius` identifies the Frobenius at a prime `p ∤ n` of `ℚ(ζₙ)`
  with the class of `p` in `(ℤ/nℤ)ˣ`: the reciprocity law for the rational field.
* `InverseGalois.CFT.Cyclotomic.Splitting` reads off from it that `p` splits completely in `ℚ(ζₙ)`
  exactly when `p ≡ 1 mod n`.
* `InverseGalois.CFT.Cyclotomic.FrobeniusSplitting` characterises complete splitting in a subfield
  by the vanishing of the Frobenius there, and produces the degree `ℓ` subfield of `ℚ(ζ_q)` for
  `ℓ ∣ q - 1` together with the power-residue description of the primes that split in it.
* `InverseGalois.CFT.Cyclotomic.Chebotarev` deduces the Chebotarev density theorem for abelian
  extensions of `ℚ`: every element of the Galois group of a subfield of a cyclotomic field is the
  Frobenius of infinitely many primes.

## The Scholz–Reichardt building block

* `InverseGalois.CFT.Cyclotomic.CyclicSubfield` builds, for a prime power `ℓ ^ N`, arbitrarily large
  primes `q ≡ 1 mod ℓ ^ N` together with the cyclic degree-`ℓ ^ N` subfield of `ℚ(ζ_q)`.
* `InverseGalois.CFT.Cyclotomic.OnePrimeRamified` pins the ramification of that subfield down to
  the single prime `q`.
* `InverseGalois.CFT.Cyclotomic.PrimeSelection` produces primes that both split completely in a
  prescribed Galois number field and lie in a prescribed residue class.
* `InverseGalois.CFT.Cyclotomic.BuildingBlock` assembles the three into the auxiliary extension the
  Scholz–Reichardt induction consumes: a cyclic extension of degree `ℓ ^ N` and level `N`, ramified
  only at a large prime that splits completely in a field fixed in advance.
* `InverseGalois.CFT.Scholz.Condition` states Serre's condition `(S_N)` — every ramified prime is
  congruent to one modulo `ℓ ^ N` and has residue degree one — and proves that it passes to a
  compositum whose factors split completely in one another.
* `InverseGalois.CFT.Scholz.Tame` shows that every field satisfying the level condition with
  `ℓ`-power degree is tamely ramified, so that the tame Kronecker–Weber theorem applies to all of
  them.
* `InverseGalois.CFT.Scholz.Selector` builds a single Galois number field containing a prescribed
  number field, a prescribed root of unity and prescribed radicals, the field whose completely
  split primes the induction selects.
* `InverseGalois.CFT.Scholz.SplitCase` treats the split case of the induction: the compositum of
  the field already realising `G` with a degree-`ℓ` field ramified at one well-chosen prime
  realises `G × C_ℓ` and again satisfies `(S_N)`.
* `InverseGalois.CFT.Scholz.PrimeChoice` shows that the primes at which the induction may branch
  are infinite in number: they are the primes splitting completely in the selector field.
* `InverseGalois.CFT.Cyclotomic.DivisorSubfield` produces, for each divisor `d` of `q - 1`, the
  cyclic subfield of degree `d` of the cyclotomic field of prime conductor `q`, together with its
  splitting law and its unramifiedness away from `q`.
* `InverseGalois.CFT.Cyclotomic.CyclotomicInertiaDeg` records that the conductor has residue degree
  one in every subfield of a cyclotomic field of prime conductor.
* `InverseGalois.CFT.Scholz.SplitStep` performs one split step concretely, producing the field, its
  Galois group as a product, its degree and its ramified primes.
* `InverseGalois.CFT.Scholz.Realization` bundles a field realising a group and satisfying `(S_N)`,
  and iterates the split step to realise every finite abelian `ℓ`-group at every level.
* `InverseGalois.CFT.Scholz.Induction` isolates the central embedding step of the induction as a
  single named property, and carries out the rest of the induction from it: granted that step,
  every finite `ℓ`-group is a Galois group over `ℚ`.
* `InverseGalois.CFT.Scholz.SplitReduction` confines the central embedding step to the surjections
  admitting no homomorphic section: a central kernel with a section splits the group as a direct
  product with a cyclic group, which the split case already realises.
* `InverseGalois.CFT.Scholz.FrattiniStep` confines it further to the surjections whose kernel lies
  in the Frattini subgroup, the remaining kernels being supplemented by a proper subgroup and hence
  admitting a section.
* `InverseGalois.CFT.Scholz.NilpotentOdd` raises the conclusion of the induction from `ℓ`-groups to
  all finite nilpotent groups of odd order, whose Sylow subgroups are `ℓ`-groups for odd `ℓ` and
  pairwise coprime.
* `InverseGalois.CFT.Scholz.NilpotentSylowTwo` drops the parity restriction on the group in favour
  of one on a single Sylow subgroup: a finite nilpotent group is realised as soon as its Sylow
  `2`-subgroups are, the odd Sylow subgroups being supplied by the induction.
* `InverseGalois.CFT.Scholz.RadicalDisjoint` proves the linear disjointness statement the induction
  needs: for odd `ℓ`, a field generated over `ℚ` by a primitive `ℓ`-th root of unity and by
  elements with rational `ℓ`-th powers has no quotient of order `ℓ`, hence no Galois subextension
  of degree `ℓ`, and so meets every degree-`ℓ` Galois field in `ℚ` only.
* `InverseGalois.CFT.Scholz.RadicalTower` realises that statement concretely, building the field
  generated by the `ℓ`-th roots of a prescribed finite set of rationals inside an algebraic closure
  as a splitting field and checking that it is a Galois number field of the required shape.

## Group extensions and the Brauer group

* `InverseGalois.CFT.GroupCohomology.OfCocycle` turns a multiplicative `2`-cocycle into a group
  extension, and `InverseGalois.CFT.GroupCohomology.ToCocycle` turns a group extension into its
  cohomology class, splitting exactly when the class vanishes.
* `InverseGalois.CFT.GroupCohomology.Classification` closes the circle: the second cohomology
  group of `G` with coefficients in `M` is in bijection with the extensions of `G` by `M`, and
  vanishes exactly when every such extension splits.
* `InverseGalois.CFT.Brauer.TensorSimple` proves that the tensor product of two central simple
  algebras is central simple, the multiplication of the Brauer group.
* `InverseGalois.CFT.Brauer.Opposite` proves that a central simple algebra tensored with its
  opposite is a matrix algebra, the inversion of the Brauer group.
* `InverseGalois.CFT.Brauer.Group` assembles the two into the abelian group structure on
  `BrauerGroup K`.
* `InverseGalois.CFT.Brauer.BaseChange` extends scalars along `K → L`, giving the homomorphism
  `BrauerGroup K →* BrauerGroup L` and the relative Brauer group `BrauerGroup.relative K L` of
  classes split by `L`.
* `InverseGalois.CFT.Brauer.Tower` records that the relative Brauer group grows with the splitting
  field: a class split by `L` is split by every extension of `L`.
* `InverseGalois.CFT.Brauer.SkolemNoether` proves the Skolem–Noether theorem: two maps of a
  simple algebra into a central simple algebra differ by conjugation by a unit.
* `InverseGalois.CFT.Brauer.Semilinear` is the semilinear refinement: a ring endomorphism of a
  matrix algebra over `L` which is `σ`-semilinear for `σ ∈ Gal(L/K)` is conjugation by a unit
  composed with `σ` on entries, and the conjugating unit is determined up to a scalar.
* `InverseGalois.CFT.Brauer.Centralizer` develops centralizer theory: the centralizer of a simple
  subalgebra of a central simple algebra is simple, the two dimensions multiply to the dimension
  of the whole, the double centralizer is the subalgebra itself, and a self-centralizing subfield
  splits the algebra.
* `InverseGalois.CFT.Brauer.CentralizerProduct` completes that picture: a central simple
  subalgebra and its centralizer multiply, `B ⊗[K] C_E(B) ≃ₐ[K] E`, and the centralizer is again
  central over `K`.
* `InverseGalois.CFT.GaloisDescent` proves Speiser's theorem: an `L`-vector space carrying a
  semilinear action of `Gal(L/K)` is the base change of its `K`-subspace of invariants.
* `InverseGalois.CFT.Brauer.CrossedProduct` builds the crossed product algebra of a Galois
  extension and a multiplicative `2`-cocycle, a central `K`-algebra of dimension `[L : K] ^ 2`.
* `InverseGalois.CFT.Brauer.CrossedProductSimple` proves that the crossed product is a simple
  ring, so that it is a central simple algebra over `K`.
* `InverseGalois.CFT.Brauer.CrossedProductCohomologous` shows that cohomologous cocycles have
  isomorphic crossed products, and that the crossed product of the trivial cocycle is the matrix
  algebra.
* `InverseGalois.CFT.Brauer.CrossedProductSplit` is the converse: a crossed product isomorphic to
  a matrix algebra comes from a cocycle that is a coboundary.
* `InverseGalois.CFT.Brauer.CrossedProductSplitting` proves that the extension `L` splits its own
  crossed products: the class of a crossed product lies in the relative Brauer group `Br(L / K)`.
* `InverseGalois.CFT.GroupCohomology.Cyclic` writes down the explicit `2`-cocycle attached to a
  cyclic group and an invariant element, and identifies its coboundaries with norms; over a cyclic
  Galois extension this is the cocycle of a cyclic algebra.
* `InverseGalois.CFT.Brauer.CyclicAlgebra` computes the cyclic case: the cyclic algebra of a
  generator of a cyclic Galois group and a unit of the base field is a matrix algebra exactly when
  that unit is a norm.
* `InverseGalois.CFT.GroupCohomology.Cohomologous` identifies equality of classes in `H²` with
  being cohomologous as multiplicative `2`-cocycles, in the explicit cochain form the crossed
  product construction consumes.
* `InverseGalois.CFT.Brauer.Kernel` computes the kernel of the crossed product construction: the
  Brauer class of a crossed product is trivial exactly when the cocycle is a coboundary, that is,
  exactly when its class in the second cohomology group vanishes; over a cyclic extension this
  identifies the trivial classes with the norms.
* `InverseGalois.CFT.Brauer.CrossedProductMul` multiplies cocycles: the crossed product of a
  product of two cocycles is a matrix algebra over the tensor product of the two crossed products,
  so Brauer classes of crossed products multiply.
* `InverseGalois.CFT.Brauer.H2Brauer` assembles this into the crossed product homomorphism from
  the second cohomology group of `Gal(L/K)` with coefficients in `Lˣ` to the Brauer group of `K`,
  and shows it is injective with image inside the relative Brauer group `Br(L / K)`.
* `InverseGalois.CFT.Brauer.Exponent` bounds the order of those classes: the cohomology of a finite
  group is killed by its order, so the Brauer class of a crossed product of `L / K` is killed by
  the degree `[L : K]`.
* `InverseGalois.CFT.Brauer.SplittingSubfield` produces, for every class split by `L`, a
  representing central simple algebra of dimension `[L : K] ^ 2` containing a copy of `L`.
* `InverseGalois.CFT.Brauer.CrossedProductRecognition` is the converse construction: a central
  simple algebra of dimension `[L : K] ^ 2` containing a copy of `L` is a crossed product of
  `L / K`.
* `InverseGalois.CFT.Brauer.H2Surjective` combines the two to invert the crossed product
  homomorphism: the relative Brauer group `Br(L / K)` of a finite Galois extension is isomorphic
  to the second cohomology group of `Gal(L/K)` with coefficients in `Lˣ`, and is killed by
  `[L : K]`.
* `InverseGalois.CFT.Brauer.CyclicBrauer` specialises to a cyclic extension: the cyclic algebra
  construction is a homomorphism from `Kˣ` to the Brauer group of `K` whose image is `Br(L / K)`
  and whose kernel is the group of norms from `L`.
* `InverseGalois.CFT.NormSubgroup` names the image of the unit group of a finite extension under
  the field norm, the subgroup of `Kˣ` that both the Brauer-theoretic and the cohomological
  descriptions of a cyclic extension quotient by.
* `InverseGalois.CFT.Brauer.CyclicNorm` reads that off as an isomorphism: for a cyclic extension
  the relative Brauer group `Br(L / K)` is `Kˣ` modulo the norms from `Lˣ`.
* `InverseGalois.CFT.Brauer.Split` proves the uniqueness half of Wedderburn's theorem in the split
  case, and deduces that a central simple algebra has trivial Brauer class exactly when it is a
  matrix algebra over the base field.
* `InverseGalois.CFT.GroupCohomology.Corestriction` builds the corestriction map of a finite-index
  subgroup in every degree, through Shapiro's lemma and the trace morphism out of a coinduced
  representation, and proves the relation `res ≫ cor = [G : S] • id`; from it, the cohomology of a
  finite group in positive degrees is killed by the order of the group.
* `InverseGalois.CFT.GroupCohomology.CyclicSurjective` puts every `2`-cocycle of a finite cyclic
  group into normal form: it is cohomologous to the explicit cocycle of an invariant element, so
  the cyclic cocycles already exhaust the second cohomology group.
* `InverseGalois.CFT.GroupCohomology.CyclicH2` reads off the Herbrand description of the second
  cohomology group of a finite cyclic group: it is the invariants modulo the norms.
* `InverseGalois.CFT.Brauer.MaximalSubfield` produces a maximal commutative subalgebra of a
  central simple algebra; inside a division algebra it is a field, and it splits the algebra, so
  every Brauer class is split by a finite subextension of the algebraic closure.
* `InverseGalois.CFT.Brauer.RealPlace` computes the Brauer group of the real place: the relative
  Brauer group `Br(ℂ / ℝ)` is cyclic of order two, generated by the Hamilton quaternions.
* `InverseGalois.CFT.Brauer.GaloisSplitting` replaces that subextension by a Galois one over a
  perfect base field, so that the relative Brauer groups of the finite Galois subextensions
  exhaust the whole Brauer group, which is therefore a torsion group.
* `InverseGalois.CFT.Brauer.RealBrauer` promotes that computation to the whole Brauer group of the
  reals, which is therefore cyclic of order two, and deduces that the Brauer group of the
  rationals is nontrivial.
* `InverseGalois.CFT.Brauer.Primary` decomposes a torsion commutative group into its primary
  components, and applies this to the Brauer group of a perfect field; a class split by an
  extension whose degree is prime to `p` has trivial `p`-primary part.
* `InverseGalois.CFT.Brauer.RationalBrauer` computes enough of the Brauer group of the rationals to
  see that it is infinite: the primes congruent to three modulo four are pairwise inequivalent
  modulo the norms of `ℚ(i)`, because a norm has even valuation at every such prime.
* `InverseGalois.CFT.Local.PadicSquares` describes the squares of a `p`-adic field for odd `p`: a
  unit of the ring of integers is a square exactly when its residue is, and a nonzero `p`-adic
  number is a square exactly when its valuation is even and its unit part is a square residue.
* `InverseGalois.CFT.Local.HilbertMap` transports isotropy along a field homomorphism, so that
  an anisotropic form over a larger field is already anisotropic over the base.
* `InverseGalois.CFT.Local.UnramifiedNormForm` computes the norm form of the unramified quadratic
  extension of a `p`-adic field for odd `p`: its values are exactly the elements of even
  valuation, so the Hilbert symbol against a nonsquare unit is multiplicative and reads off the
  parity of the valuation.
* `InverseGalois.CFT.Local.DyadicHilbert` settles the excluded prime for unit arguments: a
  dyadic isotropy question has an integral solution one of whose coordinates is a unit, so it is
  decided modulo eight, and the symbol of two dyadic units is one exactly when one of them is
  congruent to one modulo four.
* `InverseGalois.CFT.Local.DyadicHilbertMul` computes the symbol of an arbitrary pair of dyadic
  numbers from the residues modulo eight of their unit parts, and deduces that the symbol is
  bimultiplicative at the dyadic place as well.
* `InverseGalois.CFT.Local.HilbertIdentities` records that the second argument of the symbol may
  be multiplied by the negative of the first, so that the symbol of an element against itself is
  its symbol against minus one.
* `InverseGalois.CFT.SquareClasses` supplies the two induction principles that reduce a
  multiplicative identity in the square classes of the rationals to the cases where both
  arguments are minus one or a prime.
* `InverseGalois.CFT.Local.PadicHilbertMul` completes the odd local theory: every square class
  is a unit or a uniformiser times a unit, so the two norm form computations between them make
  the symbol multiplicative in each argument, give it an explicit expression as a product of
  quadratic characters, and show that the norm subgroup of a quadratic extension has index two,
  so the relative Brauer group of a quadratic extension of a `p`-adic field has order two.
* `InverseGalois.CFT.Local.LegendreHilbert` is the resulting dictionary for integer arguments:
  the symbol of two integers prime to `p` is one, and the symbol of a power of `p` times a unit
  against another is a product of Legendre symbols.
* `InverseGalois.CFT.Global.HilbertPlaces` assembles the local Hilbert symbols of a pair of
  rationals into a family indexed by the primes, and shows that the family is trivial at all but
  finitely many places, so that the product over all places makes sense.
* `InverseGalois.CFT.Global.HilbertMulPlaces` transports multiplicativity of the local symbol at
  an odd residue characteristic to the symbol of a pair of rationals at an odd finite place.
* `InverseGalois.CFT.Global.HilbertProduct` forms that product, over the real place together with
  every finite one, and records the formal properties it inherits place by place.
* `InverseGalois.CFT.Local.RamifiedNormForm` does the same for the ramified quadratic extensions:
  a `p`-adic number is a value of the norm form exactly when the parity of its valuation matches
  the quadratic character of its unit part, twisted by the unit part of the discriminant, which
  makes the Hilbert symbol against a ramified argument multiplicative as well.
* `InverseGalois.CFT.Local.HilbertMul` identifies the elements of Hilbert symbol one with the
  values of a norm form, so that they form a subgroup; when that subgroup has index two the symbol
  is multiplicative in each argument, and its triviality is exactly the triviality of the relative
  Brauer group of the quadratic extension.
* `InverseGalois.CFT.Global.OddGenerators` and `InverseGalois.CFT.Global.TwoGenerators` evaluate
  the product over all places on the pairs drawn from `-1` and the rational primes: the two
  supplementary laws and quadratic reciprocity itself.
* `InverseGalois.CFT.Global.HilbertBimul` makes the product over all places bimultiplicative, by
  collecting the multiplicativity statements proved place by place.
* `InverseGalois.CFT.Global.Reciprocity` deduces Hilbert reciprocity over the rational field, that
  the product of the local symbols of a pair of nonzero rationals over all places is one.
* `InverseGalois.CFT.Global.LocalSquare` reads the local hypothesis at a ramified odd place as a
  congruence: a trivial symbol there makes the first argument a square residue.
* `InverseGalois.CFT.Global.SquarefreeCRT` supplies the integer input for the descent: a nonzero
  integer is squarefree times a square, and a residue that is a square modulo every prime factor
  of a squarefree modulus is a square modulo the whole of it, with a small representative.
* `InverseGalois.CFT.Global.DescentTools` records that a trivial symbol may be cancelled from a
  product, the values of a binary form being a group, and that `t ^ 2 - a` is such a value.
* `InverseGalois.CFT.Global.HasseMinkowski` runs Legendre's descent on these to prove the Hasse
  principle for ternary quadratic forms over the rationals: a conic with a point at every place
  has a rational point, and the real place is already implied by the finite ones.
* `InverseGalois.CFT.Global.HasseNorm` reads that off as the Hasse norm theorem for a quadratic
  extension of the rationals, equivalently the theorem of Albert, Brauer, Hasse and Noether for
  quaternion algebras over the rational field.
* `InverseGalois.CFT.Herbrand` proves the counting theorem behind the Herbrand quotient: for a
  finite commutative group with an automorphism of finite order, the fixed points modulo the norms
  and the norm kernel modulo the differences have the same index.
* `InverseGalois.CFT.Tate.Basic` names those two subquotients the Tate groups of the module, and
  makes them functorial in equivariant homomorphisms.
* `InverseGalois.CFT.Tate.H0Norm` annihilates the upper Tate group by its own order: a fixed point
  multiplied by that order, or by any multiple of it, lies in the image of the norm; when the group
  vanishes altogether every fixed point is itself a norm.
* `InverseGalois.CFT.Tate.Exact` records the counting principle behind the hexagon: in a cyclic
  exact sequence of six finite commutative groups the orders in odd and in even position have the
  same product.
* `InverseGalois.CFT.Tate.Hexagon` builds the two connecting maps of a short exact sequence of
  modules over a cyclic group and proves the resulting six-term sequence exact at each corner.
* `InverseGalois.CFT.Tate.Herbrand` defines the Herbrand quotient as the ratio of the orders of the
  two Tate groups, and shows it multiplicative in short exact sequences and trivial on finite
  modules, so that finite submodules and finite quotients may be discarded when computing it.
* `InverseGalois.CFT.Tate.Mul` translates the formalism to a multiplicatively written module, where
  the two operators are `x ↦ σ x / x` and the product of the conjugates, so that the unit group of
  a field and the other arithmetic modules can be fed to it.
* `InverseGalois.CFT.Tate.NormalBasis` reads an element of a field in the orbit of a normal basis
  element, which identifies the additive group of a Galois extension with the functions on the
  group and the action with translation of the argument.  For a cyclic group that is the induced
  module, so both Tate groups of the additive group vanish and its Herbrand quotient is one.
* `InverseGalois.CFT.Tate.CyclicHilbert90` proves Hilbert's theorem 90 for a finite cyclic group
  acting faithfully on a field, in any universe and without choosing a base field: the partial
  products of the conjugates of an element whose conjugates multiply to one weight the conjugates
  of a test element into a Lagrange resolvent that the element scales, and Dedekind's linear
  independence of characters supplies a test element with nonvanishing resolvent.
* `InverseGalois.CFT.Tate.Galois` computes the two Tate groups of the unit group of a finite cyclic
  Galois extension: the product of the conjugates is the field norm, so Hilbert's theorem 90 says
  that the lower group is trivial, and the fixed points are the units of the base field, so the
  upper one is the base units modulo the norms.
* `InverseGalois.CFT.Tate.GaloisH0` turns that description of the upper group into an isomorphism
  with the units of the base field modulo the norms, so that its order is the norm index and the
  Herbrand quotient of the unit group is that index.
* `InverseGalois.CFT.Tate.BrauerRelative` identifies that group with the relative Brauer group of
  a cyclic extension: every class split by `L` is a crossed product and every crossed product of a
  cyclic extension is a cyclic algebra, so the cyclic algebra construction presents `Br(L / K)` as
  the units of the base field modulo the norms, and the Herbrand quotient of the unit group is the
  order of the relative Brauer group.
* `InverseGalois.CFT.Tate.Prod` computes the Tate groups of a product of two modules, where both
  operators act coordinatewise, so that the orders and hence the Herbrand quotients multiply.
* `InverseGalois.CFT.Tate.Pi` extends that computation to a finite family of modules, so that the
  orders and the Herbrand quotients are products over the index; this is the shape of the
  decomposition of the ideles of a Galois extension into the contributions of the places of the
  base field.
* `InverseGalois.CFT.Tate.Shapiro` computes the Tate groups of a module induced from a subgroup of
  a cyclic group, where the tuples are permuted cyclically and the last step applies the given
  automorphism: evaluation at one coordinate and the sum of the coordinates identify the two Tate
  groups with those of the module induced from, so the Herbrand quotients agree.
* `InverseGalois.CFT.Tate.Trivial` computes the two Tate groups when the automorphism is the
  identity, where the difference operator vanishes and the norm is multiplication by the order, and
  reads off the Herbrand quotient of the integers with trivial action, which is that order.
* `InverseGalois.CFT.Tate.TrivialLattice` extends that computation from the integers to a lattice.
  A finite product of copies of the integers has Herbrand quotient the order raised to the number
  of factors, hence so does any module with a finite basis, and hence so does any subgroup of a
  free lattice of finite rank containing a multiple of everything, the two being commensurable.
  For a group written multiplicatively the two Tate groups of the trivial action are the quotient
  by the powers and the torsion, so this is the classical index computation for a finitely
  generated abelian group.
* `InverseGalois.CFT.Tate.Congr` transports the Tate groups along an isomorphism commuting with the
  two automorphisms, so that a module presented in any other way may be compared with the shapes
  those computations handle.
* `InverseGalois.CFT.Tate.PiSplit` splits a family of modules indexed by an arbitrary set along a
  predicate on the index: the sections are the pairs consisting of the sections over the indices
  satisfying it and the sections over the others.  When the second part has vanishing Tate groups
  and the first is finite, the Herbrand quotient of the whole is the product over the first part
  only, which is how the infinitely many places of a number field yield a finite answer.
* `InverseGalois.CFT.Tate.Permutation` puts the three together for the lattice generated by a finite
  set permuted cyclically: it is a product of induced copies of `ℤ`, and its Herbrand quotient is
  the product over the orbits of the order of the stabiliser.
* `InverseGalois.CFT.Tate.Finite` shows that the order of the group annihilates both Tate groups,
  so that the Tate groups of a finitely generated module over a nontrivial cyclic group are finite
  and the Herbrand quotient of a lattice is defined with no further hypothesis.
* `InverseGalois.CFT.Tate.Isogeny` shows that an equivariant injection whose cokernel is finite
  leaves the Herbrand quotient unchanged, so that the computation for a permutation lattice applies
  to every lattice commensurable with one.
* `InverseGalois.CFT.Tate.FiniteExact` transports finiteness of the Tate groups along the exactness
  hexagon: a three term exact sequence with finite ends has a finite middle, so an equivariant
  injection with finite cokernel carries finiteness of the Tate groups in either direction and the
  comparison of Herbrand quotients needs it on one side only.
* `InverseGalois.CFT.Tate.InducedLattice` computes the Herbrand quotient of a module induced from
  the trivial action, where the norm is the identity and both Tate groups vanish, and concludes
  that a module containing an equivariant copy of such a module with finite cokernel has finite
  Tate groups and Herbrand quotient one.
* `InverseGalois.CFT.Tate.CyclicInduced` restates that conclusion for an abstract cyclic group:
  choosing a generator identifies the functions on the group with the functions on the integers
  modulo its order, and translating by the generator becomes the shift, so a module containing a
  lattice of finite index on which the generator acts by translation has Herbrand quotient one.
* `InverseGalois.CFT.Tate.Commensurable` reads that comparison for two lattices inside one abelian
  group, each carried into the other by multiplication by a nonzero integer: multiplication is then
  an equivariant injection of lattices of equal rank, so the two Herbrand quotients agree.
* `InverseGalois.CFT.Tate.Lattice` removes the hypothesis on the cokernel: between lattices of the
  same rank an equivariant injection already has finite cokernel, so two lattices related by a pair
  of maps whose composites are multiplication by a nonzero integer -- the shape a rational
  isomorphism takes once its denominators are cleared -- have the same Herbrand quotient.
* `InverseGalois.CFT.Tate.Averaging` averages a matrix over the cyclic group generated by two
  matrices of finite order, which produces an equivariant matrix from an arbitrary one and
  multiplies an already equivariant matrix by the order, so that an equivariant matrix over an
  extension ring is a combination of equivariant matrices over the base ring.
* `InverseGalois.CFT.Tate.RealForm` specialises that combination: the determinant of the generic
  equivariant matrix is a polynomial with integer coefficients that does not vanish at the point
  given by an invertible real equivariant matrix, hence does not vanish at some integer point, so
  two integer matrices of finite order conjugate over the reals admit an invertible integer
  intertwiner.
* `InverseGalois.CFT.Tate.RealHerbrand` reads that intertwiner as an equivariant injection of one
  lattice into another of the same rank, so that two lattices with isomorphic real representations
  have the same Herbrand quotient and the quotient may be computed in any convenient model of the
  representation.
* `InverseGalois.CFT.Tate.RealBasis` puts that comparison in the form it is met in: two lattices
  sitting inside one real vector space, each with a basis that is a basis of the space, and the two
  actions induced by one and the same real endomorphism.  The change of basis matrix is then the
  intertwiner, and the two Herbrand quotients agree.
* `InverseGalois.CFT.Tate.PermLattice` reads that computation back on the free lattice of a
  permuted basis, once the basis is presented as a disjoint union of cyclically shifted blocks.
* `InverseGalois.CFT.Tate.Orbit` supplies that presentation for a single orbit: a permutation
  acting transitively on a finite set identifies it with the residues modulo its cardinality, so
  the free lattice on one orbit has the Herbrand quotient of the stabiliser of a point.
* `InverseGalois.CFT.Tate.OrbitInduced` does the same for coefficients in an arbitrary module: a
  family of copies of a module indexed by an orbit, permuted with a twist on passing the last
  position, is the induced module of Shapiro's lemma, so its Herbrand quotient is that of the
  module at one point under a full turn.
* `InverseGalois.CFT.Tate.OrbitTwist` writes that twisted family as it arises in practice, as a
  family of copies of a module whose index is shifted along a permutation and whose components are
  rescaled by a group element depending on the index: the local factor of the group of ideles at a
  place of the base field, before any identification of the completions above it is chosen.
* `InverseGalois.CFT.Tate.OrbitCocycle` supplies the rescaling: choosing for every point of a
  transitive orbit the power of a generator that reaches it from a fixed base point identifies all
  the components with the component at the base point, and what is left of the generator is a shift
  of the index which is trivial except where it wraps around, where it is a full turn of the orbit.
* `InverseGalois.CFT.Tate.Family` removes the choice of an identification altogether.  A family of
  modules indexed by a set carrying a group action, together with isomorphisms between the module
  at an index and the module at its image, is acted upon not in any one of its members but in its
  group of sections; the file assembles that action out of the transport isomorphisms, the whole
  bookkeeping of equal-but-not-identical indices being absorbed into a calculus of transports
  attached to a group element and a proof that it carries one index to another.
* `InverseGalois.CFT.Tate.FamilyFree` treats the case in which the action on the index set is free.
  A section fixed by the whole group is then the sum of the conjugates of a section supported on one
  chosen point of each orbit, taking there the value of the fixed section, because for every index
  exactly one group element carries the chosen point of its orbit to it.
* `InverseGalois.CFT.Tate.FamilyOrbit` compares the two descriptions over a single orbit: choosing
  for every point the group element that reaches it from a base point identifies the sections of
  the family with copies of the module at the base point and the action of a generator with a
  twisted shift, so the Herbrand quotient of the sections is the Herbrand quotient of the module at
  the base point for a full turn of the orbit.
* `InverseGalois.CFT.Tate.FamilyRing` supplies the transport data in the form in which arithmetic
  produces it.  What a Galois automorphism carries from one place to another is a whole completion,
  a ring and not just a group, and a compatible system of ring isomorphisms along the action on the
  places induces one on the family of unit groups, written additively: the local factors of the
  group of ideles.
* `InverseGalois.CFT.Tate.FamilyRestrict` cuts a family of modules down to a family of subgroups
  carried onto one another by the transports.  The ideles that are units outside a finite set of
  places are the sections of such a restriction, the subgroup at a place being the whole local
  factor inside the set and the units of the valuation ring outside it.
* `InverseGalois.CFT.Tate.FamilyRestrictOrbit` computes the contribution of one orbit to such a
  restriction.  The stabiliser of a point of the orbit acts on the subgroup there by the restriction
  of its action on the ambient module, so an orbit where the subgroup is everything contributes what
  it contributes to the ambient family, and an orbit where the action on the subgroup is a known one
  with vanishing Tate groups contributes nothing.
* `InverseGalois.CFT.Tate.FamilySigma` splits the sections of a family whose index set is a
  disjoint union of pieces each carried into itself by the group: they are the product over the
  pieces of the sections over each piece.  Over finitely many pieces the Herbrand quotients
  multiply, over arbitrarily many pieces with vanishing Tate groups the answer is one, and in
  general only the finitely many pieces singled out by a predicate contribute as soon as the others
  are cohomologically trivial.
* `InverseGalois.CFT.Tate.FamilyReindex` pulls a family back along an equivalence of index sets
  respecting the actions, which does not change the group of sections; the decomposition of a set
  into its orbits is the case that matters.
* `InverseGalois.CFT.Tate.FamilyOrbits` puts the two together.  The Herbrand quotient of the
  sections of any family is the product over the orbits of the index set of the contribution of one
  orbit, and that contribution is the Herbrand quotient of the module at a point of the orbit under
  a full turn: exactly the local factor of the group of ideles at a place of the base field.
* `InverseGalois.CFT.Tate.NormSurjective` reads the vanishing of the upper Tate group as a statement
  about individual elements: that group is the fixed points modulo the norms, so it vanishes exactly
  when every fixed point is a norm.  Being a norm is transported by an equivariant isomorphism, and
  in a product, of two factors or of a whole family, an element is a norm as soon as each of its
  components is.
* `InverseGalois.CFT.Tate.FamilyNorm` carries that through the two identifications of the sections
  of a family, so a section is a norm as soon as its restriction to every orbit of the index set is
  one.  This is the passage from local to global that the vanishing of a Tate group is too crude to
  supply: at the places in a finite exceptional set only some of the local elements are norms, and
  the assembly has to keep track of which.
* `InverseGalois.CFT.Tate.FamilyCoboundary` is the same passage from local to global one degree
  higher, and for an arbitrary group.  A two-cocycle with values in the sections of a family is only
  acted on, at a single index, by the stabiliser of that index; if at every index its restriction to
  the stabiliser is a coboundary there, then **the cocycle is a coboundary**, by a one-cochain
  produced explicitly from the local ones and a transversal for the cosets of a stabiliser.  The
  construction keeps the values inside an invariant family of subgroups wherever the cocycle's own
  values lie there, which is what a restricted product such as the ideles requires.
* `InverseGalois.CFT.Tate.CyclicAction` states that computation for a cyclic group acting
  transitively on a finite set, where the orbit–stabiliser theorem reads the Herbrand quotient of
  the free lattice as the order of the stabiliser of a point: the form in which the places of a
  Galois extension above a fixed place of the base contribute.
* `InverseGalois.CFT.Tate.Primes` applies it to the primes of an extension of Dedekind domains
  lying over a fixed prime of the base, where the decomposition group of one of them has order the
  ramification index times the residue degree, and that product is the Herbrand quotient of the
  free lattice they span.
* `InverseGalois.CFT.Tate.Fibers` removes the transitivity hypothesis: a permutation whose orbits
  are the fibres of a map to an index set presents the set as a disjoint union of one cyclically
  shifted block per index, so that for a finite cyclic group the Herbrand quotient of the free
  lattice on any finite set it acts on is the product over the orbits of the order of the
  stabiliser of a point.
* `InverseGalois.CFT.Tate.OrbitIndex` reconciles the two ways of naming the orbits.  A map out of
  the set that is invariant under the group and admits a section meeting every orbit identifies the
  quotient by the orbit relation with the target of the map, and any invariant quantity — the order
  of a stabiliser, for instance — has the same product over either index set.  So a product over the
  orbits of the places of an extension is a product over the places of the base field.
* `InverseGalois.CFT.Tate.OrbitRange` reconciles them the other way round, when the orbits that
  matter are named by an abstract set mapped equivariantly and injectively into the index set.  Such
  a map induces an injection on orbits whose image is the orbits meeting the range, and it preserves
  stabilisers, so the two ways of naming the chosen places give the same product of the orders of
  the decomposition groups.
* `InverseGalois.CFT.Tate.InfinitePlaces` applies that to the infinite places of a Galois extension
  of number fields, which the Galois group permutes with the places of the base field as the set of
  orbits: the Herbrand quotient of the free lattice they span is the product of the orders of the
  decomposition groups, and each of those is two at a ramified place of the base and one elsewhere.
* `InverseGalois.CFT.Tate.Augmentation` cuts a lattice down by an invariant surjection onto the
  integers with trivial action, the sum of the coordinates in the case of a permuted basis: the
  kernel is again stable, and since the quotient contributes the factor `n`, the Herbrand quotient
  of the kernel is that of the lattice divided by the order of the group.  This is the shape of the
  unit lattice, whose real representation is the trace-zero part of the permutation representation
  on the infinite places.
* `InverseGalois.CFT.Tate.Surjection` records the other elementary reduction: an equivariant
  surjection has an invariant kernel, and when that kernel is finite the source and the target have
  the same Herbrand quotient, so a finite torsion subgroup may be discarded.
* `InverseGalois.CFT.Units.GaloisAction` lets a field automorphism act on the units of the ring of
  integers, and recognises the roots of unity by the infinite places, so that they form an
  invariant subgroup.
* `InverseGalois.CFT.Units.UnitLattice` embeds the units logarithmically at all the infinite places
  at once.  The kernel is the group of roots of unity, and forgetting one place identifies the
  image with the unit lattice of Dirichlet's theorem, so it is a lattice of rank one less than the
  number of places; the Galois group acts on it by permuting the places, and the units and the
  lattice have the same Herbrand quotient.
* `InverseGalois.CFT.Units.Herbrand` computes that quotient.  Adjoining the vector of the
  multiplicities to the unit lattice gives a lattice of the full rank whose real span is that of
  the free lattice on the infinite places, with the two actions induced by the same permutation of
  coordinates: the Herbrand quotient of the units, times the degree of the extension, is therefore
  the product of the orders of the decomposition groups at the infinite places, one factor of two
  for each ramified real place of the base field.
* `InverseGalois.CFT.Tate.Restrict` restricts an automorphism to an invariant subgroup, so that a
  lattice inside an ambient group carries an action of the cyclic group generated by the
  automorphism, and records the finiteness statements a lattice and an extension of lattices
  inherit.
* `InverseGalois.CFT.Tate.QuotientFixed` lifts a class of a quotient fixed by the induced
  automorphism to a fixed point of the ambient group, whenever the Tate group `Ĥ⁻¹` of the
  subgroup vanishes: the difference between a representative and its image lies in the subgroup and
  has norm zero, so it can be subtracted away.
* `InverseGalois.CFT.Units.Places` lets a field automorphism act on the height one primes of the
  ring of integers, where it carries the factorisation of a principal fractional ideal onto the
  factorisation of the image, so that the order of an element at a prime is the order of its image
  at the image of the prime; over a Galois extension the primes above a fixed prime of the base
  form one orbit.
* `InverseGalois.CFT.Units.SUnit` names the `S`-units, the elements of order zero at every prime
  outside a chosen set, together with their vector of orders at the chosen primes: the units of the
  ring of integers are exactly the `S`-units whose vector vanishes, and the Galois action on the
  `S`-units matches the permutation of the primes on the vectors.
* `InverseGalois.CFT.Units.SUnitHerbrand` computes the Herbrand quotient of the `S`-units of a
  cyclic extension.  A power of every prime is principal, so the lattice of order vectors is
  commensurable with the free lattice on the chosen primes and has its Herbrand quotient, the
  product over the orbits of the order of a decomposition group; the short exact sequence of the
  units, the `S`-units and that lattice then multiplies this by the contribution of the infinite
  places.
* `InverseGalois.CFT.Units.SUnitIndex` runs the same short exact sequence with no action at all.
  The units of the ring of integers then contribute the rank of the unit lattice and the lattice of
  order vectors the number of chosen primes, so the Herbrand quotient of the `S`-units is the given
  order raised to their sum.  The torsion of the `S`-units is the group of roots of unity, because
  a root of unity has order zero at every prime, so when the field contains enough of them the
  index of the powers in the group of `S`-units is that order raised to the number of places of
  `S`, the infinite places together with the chosen finite primes.
* `InverseGalois.CFT.SubgroupIndex` splits a relative index along a third subgroup: for `B` inside
  `A` and any `C`, inserting the subgroup `A` cuts out of `B ⊔ C` writes the index of `B` in `A` as
  the index of `B ⊔ C` in `A ⊔ C` times the index of `B ⊓ C` in `A ⊓ C`, the two factors coming
  from the second isomorphism theorem and from the modular law.
* `InverseGalois.CFT.Kummer.PowBasis` turns such an index into a radical extension.  The quotient
  of a subgroup of a commutative group by the `p`-th powers of its elements is killed by `p`, so
  it is a vector space over the field with `p` elements and a quotient of order `p ^ s` has a basis
  of `s` elements; lifting that basis gives a family of `s` elements of the subgroup which is
  independent modulo `p`-th powers and spans the subgroup modulo them.  When the subgroup consists
  of units of a field and is saturated, in the sense that an element whose `p`-th power lies in it
  already lies in it, the family is independent in the whole multiplicative group and therefore
  carries a Kummer setup: the extension generated by `p`-th roots of the family is Galois of degree
  `p ^ s` and contains a `p`-th root of every element of the subgroup.
* `InverseGalois.CFT.Kummer.SUnitExt` feeds the `S`-units into that machine.  They are saturated,
  an element whose power has order zero outside `S` having order zero there already, and their
  quotient by the `p`-th powers has order `p` raised to the number of places of `S`; so for a
  number field containing the `p`-th roots of unity the extension generated by the `p`-th roots of
  the `S`-units is Galois of that degree, and every `S`-unit acquires a `p`-th root in it.
* `InverseGalois.CFT.Kummer.LocalPower` reads a local `p`-th power off the decomposition group.
  The decomposition group at a prime of a Galois extension of number fields fixes a radical
  exactly when the radicand is a `p`-th power in the completion of the base below that prime, the
  base containing the `p`-th roots of unity: an element of the completion fixed by the
  decomposition group comes from the completion below, and two `p`-th roots of the same element
  differ by a root of unity, which is already in the base.  So an element fixed by every
  decomposition group in a family generating the Galois group is fixed by the whole group, which
  is what turns a local condition at finitely many places into a global one.  The same holds at an
  infinite place, the completion of the base below being the fixed field of the decomposition group
  there too.
* `InverseGalois.CFT.Kummer.Pairing` compares two radicals through their exponent vectors.  Writing
  an element of the subgroup as a product of powers of the power basis times a `p`-th power, the
  automorphism which multiplies the `i`-th radical by the `cᵢ`-th power of the root of unity fixes
  the radical of an exponent vector `m` exactly when `p` divides `∑ cᵢ mᵢ`.  So if every
  automorphism fixing the radical of one element fixes the radical of another, every vector
  orthogonal modulo `p` to the first exponent vector is orthogonal to the second, and over the
  field with `p` elements that forces the two vectors to be proportional: the second element is,
  modulo `p`-th powers, a power of the first.
* `InverseGalois.CFT.Kummer.GlobalPower` assembles the global step.  The Galois group of the
  radical extension is abelian of exponent `p`, so the field cut out by a radical of `a` is an
  intermediate field whose fixing subgroup is generated by the decomposition groups at the places
  splitting completely in it.  An element of the subgroup which is a `p`-th power in the completion
  at each of those places therefore has a radical fixed by every automorphism fixing the radical of
  `a`, and comparing exponent vectors writes it as a power of `a` times a `p`-th power.
* `InverseGalois.CFT.Kummer.RootIndex` measures how much of the radical extension a single radical
  sees.  A `p`-th root generates a subextension of degree at most `p`, its minimal polynomial
  dividing the monic polynomial `X ^ p - a`, and the degree of that subextension is the index of
  the subgroup fixing the root; when the Galois group is a `p`-group the index is a power of `p`,
  and it is not one unless the radicand was already a `p`-th power downstairs, so it is exactly `p`.
* `InverseGalois.CFT.Kummer.LocalSurjective` prescribes the local behaviour of an `S`-unit.  The
  places splitting completely in the field cut out by a radical of `a` supply a finite set `T` of
  primes of the base, disjoint from `S`, whose decomposition groups generate a subgroup of index
  `p`; the `S`-units map to the product over `T` of the units of the valuation ring modulo their
  `p`-th powers, a group of order `p` at each place since the place does not divide `p` and the
  base has the `p`-th roots of unity.  The kernel of that map is exactly the subgroup generated by
  `a` and the `p`-th powers, by the global step above, and its index matches the order of the
  target, so the map is surjective: a prescribed family of local units is met by a global `S`-unit
  up to `p`-th powers.
* `InverseGalois.CFT.Kummer.Denominator` clears a denominator without disturbing a chosen place.
  An element of the fraction field of a Dedekind domain which is integral at that place can be
  multiplied into the domain by a scalar congruent to one there: the denominator is divisible by
  only finitely many primes, and the Chinese remainder theorem prescribes a single element lying in
  the required power of each of them while staying a unit at the place one cares about.
* `InverseGalois.CFT.Kummer.Unramified` bounds the ramification of a radical extension.  An element
  of the inertia group at a place multiplies each radical by a `p`-th root of unity; scaling the
  radicand into the ring of integers by a factor which is a unit below keeps the radical a unit at
  the place, so the root of unity is congruent to one there.  But a nontrivial `p`-th root of unity
  divides `p`, which the place avoids, so the element fixes every radical and the radicals generate:
  the extension is unramified at every place away from the exponent at which the radicands are
  units.
* `InverseGalois.CFT.Kummer.SUnitUnramified` applies that bound to the extension generated by the
  `p`-th roots of a basis of the `S`-units.  Its radicands are `S`-units, so they have valuation one
  at every prime outside `S`, and once `S` carries every prime above `p` the exponent is avoided
  there as well: the extension is unramified at every prime outside `S`.
* `InverseGalois.CFT.Kummer.PowerCriterion` turns the local conditions into a global power.  An
  element of a number field with the `p`-th roots of unity which is not a `p`-th power there cuts
  out, through the polynomial `X ^ p - b`, a cyclic extension of degree `p`; the criterion above
  makes that extension split completely at the infinite places and at the places of a first set
  where the element is a local `p`-th power, and the ramification bound makes it unramified outside
  that set and a second, auxiliary one.  Every idele which is a local `p`-th power at the auxiliary
  places and a unit outside the two sets is then a norm from the extension, and those ideles
  together with the principal ones exhaust the ideles, so the first inequality bounds the degree by
  one: the element was a `p`-th power after all.
* `InverseGalois.CFT.Kummer.SecondInequality` counts the norm index of a cyclic radical extension
  of prime degree.  The extension generated by the `p`-th roots of all the `S`-units has degree
  `p ^ s` over the base, where `s` counts the places of `S` together with the infinite ones; the
  subgroup fixing a `p`-th root of the radicand has index `p`, and the auxiliary places supplied by
  the surjectivity above index a family of decomposition groups generating it, so their number is
  `s - 1`.  The radicand is a local `p`-th power at those places, so the extension splits completely
  there, and it is unramified outside the two sets, so the ideles carrying the local powers are
  norms.  Their index together with the principal ideles is `p ^ (2 * s)` divided by `p ^ (2 * s
  - 1)`, which is the degree; the first inequality gives the reverse bound.
* `InverseGalois.CFT.Kummer.CyclotomicDescent` removes the root of unity from the base field.
  Adjoining a primitive `p`-th root of unity to the base field is an extension of degree dividing
  `p - 1`, and doing the same to an extension of degree `p` produces the compositum of the two,
  which is normal over the base field and again of degree `p` over the new base field: its degree
  is divisible by `p` because the degree of the new base field is prime to `p`, and it is at most
  `p` because the degree of the root of unity can only drop when the base field grows.  Enlarging
  the base field by an extension of degree prime to the degree can only increase the norm index, so
  the count for the new pair bounds the count for the old one, and the first inequality bounds the
  latter from below by the degree.
* `InverseGalois.CFT.Kummer.CyclicIndex` counts the norm index of an arbitrary cyclic extension.
  The count is multiplicative along a tower up to a divisibility: passing to the middle field
  shrinks the subgroup generated by the principal ideles and the norms, and the norm to the base
  field carries the ideles of the middle field onto the larger subgroup modulo the smaller one.  A
  cyclic group of composite order has a subgroup of prime index, whose fixed field is a step of
  prime degree with the whole extension again cyclic above it, so induction on the degree reduces
  the count to the prime case, and the first inequality matches the resulting bound.
* `InverseGalois.CFT.Units.HasseNorm` deduces the norm theorem for a cyclic extension.  The units
  of the top field, its ideles and its idele classes form a short exact sequence of modules over the
  cyclic Galois group, since the diagonal embedding is injective and equivariant.  The idele class
  group has Herbrand quotient the degree and its zeroth Tate group has order the norm index, which
  is the degree as well, so the other Tate group of the idele class group is trivial; exactness of
  the Tate hexagon at the zeroth group of the units then makes the map to the zeroth group of the
  ideles injective.  Reading the Tate norm operator of a generator as the product of the conjugates
  identifies it with the field norm, so a unit of the base field whose principal idele is the norm
  of an idele is the norm of a unit of the extension.
* `InverseGalois.CFT.Units.LocalNorm` states that theorem one place at a time.  The decomposition
  group at a place acts faithfully on the completion there and commutes with the scalars of the
  completion of the base, and every automorphism of the completion over the completion of the base
  is the action of one of its elements, so the field norm of the local extension is the product of
  the conjugates under the decomposition group, which is the norm operator of the Tate formalism for
  a full turn of the orbit of the place.  Enlarging the support of an idele of the base field
  together with the places lacking a fixed uniformizer to a finite invariant set of places, the
  local-to-global criterion then exhibits an idele that is a local norm at every place as the norm
  of an idele, and the norm theorem turns a unit of the base field that is a local norm everywhere
  into the norm of a unit of the extension.
* `InverseGalois.CFT.Local.AdicAction` carries a field automorphism to the adic completions: it
  preserves the valuation of an element up to moving the prime, so it is an isometry of the valued
  field at a prime onto the valued field at the image prime, and extends by continuity to a ring
  isomorphism of the completions.  The automorphisms fixing the prime therefore act on the
  completion by isometric ring automorphisms, and preserve its ring of integers.
* `InverseGalois.CFT.Local.AdicFamily` does this for every prime at once.  The transports satisfy
  the two compatibilities on the image of the field, which is dense in each completion, so the
  completions at the finite places are a family of rings carrying an action of the Galois group,
  and the group acts on the sections of the family and on the sections of the family of unit
  groups.
* `InverseGalois.CFT.Local.UnitValuation` reads the valuation of a unit of a discretely valued
  field as a homomorphism onto the integers, whose kernel is the unit group of the valuation ring.
  A group acting by isometries acts trivially on the quotient, so the resulting short exact
  sequence multiplies the Herbrand quotient of the units of the valuation ring by the order of the
  group to give the Herbrand quotient of the units of the field.
* `InverseGalois.CFT.Local.AdicUnits` applies this to the completion of a number field at a prime,
  where the group is the decomposition group of the prime.
* `InverseGalois.CFT.Local.AdicResidue` supplies the two finiteness inputs for such a completion:
  the valuation of a uniformizer is already the value just below one, and the integers of the base
  are dense enough in the valuation ring that the graded piece at zero is a quotient of the residue
  field of the prime, hence finite.
* `InverseGalois.CFT.Local.AdicHerbrand` discharges the remaining hypotheses of the general
  computation for such a completion.  The characteristic of the residue field is a prime lying in
  the place, so its valuation is less than one and it is a residue characteristic in the sense the
  exponential needs; every graded piece is finite because the one at zero is; and an automorphism
  acting trivially on the completion already acts trivially on the dense subfield, so the
  decomposition group acts faithfully.  The units of the valuation ring therefore have Herbrand
  quotient one, the units of the completion have Herbrand quotient the order of the decomposition
  group, and both Tate groups of the units of the valuation ring vanish when the decomposition
  group fixes a uniformizer.
* `InverseGalois.CFT.Local.NormIndex` divides that quotient.  The decomposition group acts
  faithfully on the completion, which is a field, so Hilbert's theorem 90 applies verbatim and the
  lower Tate group of the units of the completion vanishes.  The upper one therefore has order the
  order of the decomposition group: the norms from the completion form a subgroup of the units of
  index the local degree.  Annihilating that group by its order, every multiple of the local degree
  of a unit fixed by the decomposition group is a local norm.
* `InverseGalois.CFT.Units.EquivariantLabel` records the one fact that a labelling of a set acted
  on by a group by the points of another such set needs to satisfy for the two to have the same
  decomposition groups: an injective equivariant map identifies the stabiliser of a point with the
  stabiliser of its label.
* `InverseGalois.CFT.Units.LocalIdele` assembles the completions above one place of the base field
  into the local factor of the group of ideles there.  Those places form a single orbit, so
  transporting all of the factors to a chosen one presents the factor as the module induced from
  the decomposition group, and its Herbrand quotient is the order of that group.
* `InverseGalois.CFT.Units.AdicOrbit` says the same thing in the language of families of modules,
  where no labelling of the orbit is needed: restricting the family of all completions to one orbit
  and reading the action of the stabiliser of a point off the transports gives the local factor
  Herbrand quotient the order of the decomposition group.
* `InverseGalois.CFT.Local.InfiniteAction` builds the same picture at an infinite place.  An
  automorphism fixing such a place preserves its absolute value, so it is an isometry of the field
  for the metric of the place and extends to the completion there; the decomposition group of the
  place therefore acts on the completion by ring automorphisms, faithfully because it already acts
  faithfully on the dense subfield.
* `InverseGalois.CFT.Local.InfiniteFamily` is the archimedean counterpart of the family of adic
  completions: the completions at the infinite places carry an action of the Galois group as a
  family of rings, checked on the image of the field and extended by continuity.
* `InverseGalois.CFT.Local.ComplexHerbrand` computes the local Herbrand quotient at a ramified real
  place.  The completion is the complex numbers, complex conjugation generates the Galois group of
  `ℂ / ℝ`, and the norms from `ℂˣ` are the positive reals, so the Herbrand quotient of `ℂˣ` is the
  index two of the norms.
* `InverseGalois.CFT.Local.InfiniteHerbrand` combines the two cases.  A decomposition group at an
  infinite place has order one or two, and it has order two exactly when the place is complex above
  a real place, where the nontrivial element acts by complex conjugation.  So the units of the
  completion have Herbrand quotient the order of the decomposition group, exactly as at a finite
  place.
* `InverseGalois.CFT.Local.InfiniteNormIndex` divides that quotient by its denominator.  The
  decomposition group acts faithfully on the completion, which is a field, so Hilbert's theorem 90
  makes the lower Tate group of the units vanish and the upper one has order the local degree.
  Annihilating that group by its order, every multiple of the local degree of an element of the
  completion fixed by the decomposition group is a local norm.
* `InverseGalois.CFT.Units.InfiniteIdele` assembles the infinite places above one infinite place of
  the base field into the local factor of the ideles there, by the same induction from the
  decomposition group as at a finite place.
* `InverseGalois.CFT.Units.InfiniteOrbit` is the same computation in the language of families of
  modules, restricting the family of completions at all the infinite places to one orbit.
* `InverseGalois.CFT.Units.ArchimedeanIdeles` multiplies those local factors together.  The infinite
  places of the extension break into one orbit above each infinite place of the base field, so the
  archimedean part of the group of ideles has Herbrand quotient the product of the orders of the
  decomposition groups: the same as the free lattice on the infinite places, which is the shape of
  the unit lattice.  The two will cancel in the idele class group.
* `InverseGalois.CFT.Units.AdicSIdeles` cuts the finite part of the ideles down to those that are
  units outside a set of places.  The local subgroup is the whole group of units of the completion
  at a place of the set and the units of the valuation ring elsewhere; the Galois transports are
  isometries, so those subgroups form an invariant family, and an orbit above a place of the set
  contributes the order of the decomposition group while an unramified orbit outside it contributes
  nothing.
* `InverseGalois.CFT.Units.AdicIdeleHerbrand` multiplies the finite local factors together.  When
  the chosen places are the range of an equivariant injection from a finite index set and every
  other place is unramified, the ideles that are units outside them have Herbrand quotient the
  product over the orbits of the index set of the orders of the decomposition groups: the same
  factor that appears in the Herbrand quotient of the `S`-units.
* `InverseGalois.CFT.Units.SIdeleHerbrand` puts the archimedean and the finite factors together.
  The ideles that are units outside the chosen places have Herbrand quotient the product of the
  orders of the decomposition groups at the infinite places of the base field and at the orbits of
  the chosen finite places, which is exactly the Herbrand quotient of the group of `S`-units times
  the degree of the extension.  Dividing the one by the other will leave a group of Herbrand
  quotient the degree, which is the first inequality of class field theory.
* `InverseGalois.CFT.Local.AdicUnramified` supplies the unramifiedness hypothesis that the last two
  computations run on.  A prime is unramified over the base exactly when the ideal generated there
  by the prime below is not contained in its square, and then some element of the base ring lies in
  the prime and not in its square, so it has valuation exactly one; its inverse is a unit of the
  completion of valuation one, fixed by the whole Galois group because it comes from the base field.
  The places where this fails divide the different ideal, so there are only finitely many of them.
* `InverseGalois.CFT.Units.ClassSet` supplies the other input the comparison needs, the finiteness
  of the class number.  Choosing one fractional ideal in each ideal class and collecting the primes
  where those finitely many representatives are nontrivial gives a finite set of primes away from
  which every system of orders vanishing at all but finitely many primes is realised by a single
  element of the field; enlarging the set to the union of its translates makes it stable under the
  Galois group without disturbing that property.
* `InverseGalois.CFT.Units.BaseChangeIndex` compares the norm index over two base fields.  The norm
  of an idele of the base field is the degree times that idele, because its conjugates are all
  itself, and the norm of a principal idele is principal, because the sum of the conjugates of a
  unit is fixed by the Galois group.  Hence the norm from a larger base field descends to the
  quotients, and if the degree of the enlargement is prime to the degree of the extension then that
  descended map is surjective, so the index over the smaller base field divides the index over the
  larger one.
* `InverseGalois.CFT.Units.LocalEmbedding` and `InverseGalois.CFT.Units.SIdeleClass` carry out the
  division.  A nonzero element of the field is a unit of every completion, and at a finite place its
  local valuation is minus its order there, so an `S`-unit lands in the units of the valuation ring
  away from the chosen places and the field embeds diagonally in the ideles that are units outside
  them; the embedding is injective because a number field embeds in the completion at an infinite
  place, and it commutes with the Galois action because the transports at all places are induced by
  the automorphism itself.  Multiplicativity of the Herbrand quotient along the resulting short
  exact sequence then cancels the two products of orders of decomposition groups and leaves the
  degree of the extension as the Herbrand quotient of the quotient group.  The finiteness that
  multiplicativity requires is not proved by generation, which is unavailable for groups this large,
  but read off from the computation: an infinite group has cardinality zero, so a Herbrand quotient
  that is a positive product of orders already certifies finiteness for the two outer terms, and
  exactness carries it to the quotient term.
* `InverseGalois.CFT.Units.Idele` introduces the full group of ideles, without reference to a
  chosen finite set of places: the elements of the product of all the local unit groups whose
  component is a unit of the valuation ring at all but finitely many finite places.  The
  finiteness condition survives the Galois action because the transports between completions are
  isometries and the action merely permutes the places, and it holds for the diagonal image of an
  element of the field because such an element has nonzero order at only finitely many primes.
* `InverseGalois.CFT.Units.IdeleClass` divides the ideles by the diagonal image of the
  multiplicative group of the field and identifies the result with the quotient already computed.
  The ideles that are units outside the chosen places include into the ideles, and the comparison
  rests on two facts about a set of places large enough to carry the ideal classes: every idele
  differs from one of the smaller group by a principal idele, because the system of local
  valuations of an idele vanishes at all but finitely many places and is therefore realised away
  from the chosen ones by a single element of the field; and an element of the field whose diagonal
  image lies in the smaller group has order zero away from the chosen places, so it is an `S`-unit.
  The induced isomorphism of quotients commutes with the Galois action, so the idele class group
  has the Herbrand quotient already computed, namely the degree of the extension.
* `InverseGalois.CFT.Units.IdeleClassFixed` identifies the idele classes fixed by a generator of a
  cyclic Galois group with the classes of the fixed ideles.  The difference between a representative
  of a fixed class and its image is a principal idele whose norm vanishes, and Hilbert's theorem 90
  for the units of the field, which holds because the group acts faithfully on a field, presents it
  as the difference of a principal idele; subtracting that off makes the representative fixed.
* `InverseGalois.CFT.Units.FirstInequality` removes the hypotheses on the chosen set of places and
  draws the conclusion.  A finite set of places can always be enlarged to a finite one invariant
  under the Galois group by taking the union of its translates, and the two demands made of the
  chosen set are each satisfied by some finite set: finitely many places suffice to represent every
  system of orders, and only finitely many places fail to carry a uniformizer fixed by the
  decomposition group.  The union of the two therefore works, so for a cyclic extension the idele
  class group has Herbrand quotient the degree unconditionally.  Since the quotient is a positive
  rational, both Tate groups are finite, and the order of the zeroth one is the degree times the
  order of the other and hence at least the degree.
* `InverseGalois.CFT.Units.CyclicTrivial` reads the first inequality as a triviality criterion.  If
  every idele class fixed by the Galois group of a cyclic extension is a norm then the zeroth Tate
  group of the idele class group has a single element, so the degree, which the first inequality
  bounds by its order, is at most one; contrapositively a nontrivial cyclic extension always has a
  fixed idele class outside the norms.
* `InverseGalois.CFT.Units.PlaceComap` relates the two adic valuations attached to a prime and the
  prime below it: they differ by the ramification index, which is at least one, so the inclusion of
  the base field is uniformly continuous for the two adic topologies and extends to a map of the
  completion of the base at a prime into the completion of the extension at any prime above it.
* `InverseGalois.CFT.Units.CompletionFinite` shows that map makes the completion above a finite
  extension of the completion below, of degree at most the degree of the global extension.  A
  finite spanning set of the extension over the base spans, over the completion of the base, a
  finite dimensional and therefore closed subspace which contains the dense image of the extension.
* `InverseGalois.CFT.Units.CompletionGalois` shows the extension of completions is Galois with
  Galois group the decomposition group.  The extension is a splitting field, because the separable
  polynomial split by the global extension still splits in the completion and the subalgebra its
  roots generate is closed and dense; and the decomposition group exhausts the Galois group because
  an automorphism over the completion of the base is continuous, hence preserves the unit ball and
  restricts to the extension.  So the elements fixed by the decomposition group are exactly those
  coming from the completion of the base.
* `InverseGalois.CFT.Units.CompletionUnits` passes that description to the unit groups: a fixed
  unit comes from the completion of the base and is nonzero there, hence is a unit below.
* `InverseGalois.CFT.Units.OrbitPlaces` identifies the orbits of the Galois group on the height one
  primes of the extension with the height one primes of the base, transitivity giving injectivity
  and the existence of a prime above giving surjectivity.
* `InverseGalois.CFT.Units.AdicFixed` combines the two to describe the finite part of the ideles
  fixed by the Galois group.  A family of local units of the base determines one of the extension by
  taking, at each prime, the image of the unit at the prime below, and the families so obtained are
  exactly the fixed ones: a fixed family has its value at a prime fixed by the decomposition group
  there, hence coming from below, and its values at the other primes of the same orbit are the
  transports of that one.
* `InverseGalois.CFT.Units.InfiniteComap` builds the same tower at an infinite place.  An infinite
  place of the extension restricts to one of the base and the inclusion of the base is then an exact
  isometry, with no ramification index to correct for, so it extends to the completions and makes
  the completion above a finite dimensional normed algebra over the completion below.
* `InverseGalois.CFT.Units.InfiniteGalois` runs the Galois theory of that tower.  Since the
  structure map is an isometry, an automorphism over the completion below is bounded on the powers
  of an element and therefore norm preserving, hence restricts to the extension; the completion
  above is a splitting field over the completion below, and the elements, and so also the units,
  fixed by the decomposition group are exactly those coming from below.
* `InverseGalois.CFT.Units.InfiniteFixed` runs the argument of `AdicFixed` at the infinite places.
  A family of local units of the base field gives one of the extension by taking, at each place, the
  image of the unit at the place below, and again the families so obtained are exactly the fixed
  ones, the Galois group permuting the places above a place of the base transitively.
* `InverseGalois.CFT.Units.IdeleFixed` puts the two halves together.  The Galois action on the
  ideles is a homomorphism into the automorphism group, so the automorphisms fixing a given idele
  form a subgroup and being fixed by a generator of a cyclic group is being fixed by the group; and
  an idele of the base field gives one of the extension, the finiteness condition surviving because
  the places where the result fails to be a unit of the valuation ring lie above the finitely many
  places where the given idele does.  The ideles fixed by the Galois group are exactly the ideles of
  the base field.
* `InverseGalois.CFT.Units.IdeleNorm` is the norm map on the ideles of a Galois extension.  The sum
  of the conjugates of an idele is fixed by every automorphism, an automorphism merely permuting the
  group, hence is the image of a unique idele of the base field, and that idele is the norm.  For a
  cyclic group the sum of the conjugates is the norm of the Tate formalism taken for a generator,
  because the powers of a generator below its order run through the group exactly once.  The
  diagonal is compatible with the passage between the two fields, because at every place the
  structure map of the completion above over the completion below carries the image of an element of
  the base field to its image in the extension.
* `InverseGalois.CFT.Units.PlaceTower` compares the places and the completions of a tower of number
  fields.  A place of the top field lies over a place of the middle field, which lies over a place
  of the bottom field, and that is the place of the bottom field the place of the top field lies
  over directly; the two ways of getting from the completion of the bottom field into the completion
  of the top field both extend the dense inclusion of the bottom field, so they agree.
* `InverseGalois.CFT.Units.IdeleTower` puts those comparisons together: the inclusions of the ideles
  of a tower compose to the inclusion at the bottom.
* `InverseGalois.CFT.Units.PlaceRestrict` moves a place of a tower by an automorphism of the top
  field.  Such an automorphism restricts to the middle field, the place of the middle field below
  the moved place is the moved place below, and the isomorphisms of completions attached to the two
  automorphisms agree on the completion of the middle field, both being continuous and agreeing on
  the dense image of that field.
* `InverseGalois.CFT.Units.IdeleRestrict` assembles that place by place: the inclusion of the ideles
  of the middle field intertwines the action of an automorphism of the top field with the action of
  its restriction.
* `InverseGalois.CFT.Units.IdeleNormTower` deduces that the norm on the ideles of a tower is the
  norm to the middle field followed by the norm from the middle field.  Lifting an automorphism of
  the middle field and multiplying by an automorphism fixing it is a bijection from the product of
  the two Galois groups onto the Galois group of the whole extension, so the two sums of conjugates
  have the same terms, and the inclusion of the ideles of the bottom field is injective.  This is
  what lets a statement about the norms of a cyclic extension be applied inside a solvable tower,
  one step at a time.
* `InverseGalois.CFT.Units.IdeleClassIndex` identifies the zeroth Tate group of the idele class
  group with the quotient of the ideles of the base field by the principal ideles together with the
  norms, which is the classical shape of the first inequality.  An idele of the base field gives an
  idele class of the extension which is fixed, and every fixed class arises that way because a fixed
  class is the class of a fixed idele.  A class dies exactly when the idele differs from a norm by a
  principal idele of the extension fixed by the Galois group, and such a principal idele comes from
  a unit of the base field, the fixed field of the whole group being the base field.
* `InverseGalois.CFT.Units.NormIndex` turns the first inequality into a triviality criterion in
  terms of norms.  If the principal ideles together with the norms exhaust the ideles of the base
  field then the index they bound is one, so the degree is one and the extension is trivial.  The
  hypothesis is an exact equality of subgroups, so no topology on the ideles is needed.
* `InverseGalois.CFT.Units.SolvableNorm` upgrades that criterion from a cyclic extension to a
  solvable one.  A nontrivial finite solvable group has a nontrivial complex character, and the
  quotient by the kernel of a character is a finite subgroup of the complex units, hence cyclic; the
  fixed field of the kernel is therefore a nontrivial cyclic subextension, and it inherits the
  hypothesis because the norms of a tower compose.
* `InverseGalois.CFT.Units.SplitNorm` produces the norms when the Galois group permutes the places
  freely, which is what happens when every place of the base field splits completely.  An idele of
  the base field, read in the extension, is fixed, and the free action lets it be written as the sum
  of the conjugates of a section supported on one place above each place of the base field, so it is
  a norm; a solvable extension in which every place splits completely is therefore trivial.
* `InverseGalois.CFT.Units.Decomposition` shows that the decomposition groups generate a solvable
  Galois group.  The subgroup they generate is normal, and in its fixed field every place of the
  base field splits completely: an automorphism of that subextension fixing a place is the
  restriction of an automorphism of the top field fixing a place above it, obtained by correcting
  an arbitrary lift
  with an automorphism over the subextension, and such an automorphism lies in the subgroup and so
  restricts to the identity.
* `InverseGalois.CFT.Units.PowIdele` bounds the index of the `n`-th powers inside the ideles that
  are units outside a finite set of places.  The two subgroups involved are products of local
  subgroups differing only where `n`-th powers were imposed, so their relative index is the product
  of the local indices there, and when the imposed places carry every place at which `n` is not a
  unit and the base contains a primitive `n`-th root of unity the product formula evaluates it as
  `n` raised to twice the number of places involved.
* `InverseGalois.CFT.Units.PrimeAbove` records that a prime lies above a natural number in the
  three ways the counting needs it: membership of the number in the prime, the adic valuation of the
  number, and the normalised absolute value at the associated finite place all say the same thing.
* `InverseGalois.CFT.Units.SUnitValuation` reads the defining property of an `S`-unit as a
  valuation: the order of a nonzero element at a prime vanishes exactly when its adic valuation
  there is one, so an `S`-unit has valuation one at every prime outside `S`.
* `InverseGalois.CFT.Units.PowSIdeleClass` throws the principal ideles into that comparison.  The
  ideles of the set of places together with the principal ideles are all the ideles, the set
  carrying the ideal classes; the principal ones among them are the units of the set, and the
  principal ones among the local `p`-th powers are the `p`-th powers of those units, by the
  criterion for a local power to be a global one.  Splitting a relative index along the principal
  ideles then turns the two known indices into the index of the local powers together with the
  principal ideles inside all the ideles.
* `InverseGalois.CFT.Units.PowSIdeleNorm` proves that those local powers are norms from a cyclic
  extension of prime degree.  A `p`-th power coming from the base is a local norm at any place,
  because the order of a decomposition group divides the degree; above the auxiliary places the
  decomposition group is trivial, so every local element is a norm; and outside the two sets the
  extension is unramified, so a unit of the valuation ring is a norm.  The places above the two sets
  form a finite invariant set, and the local-to-global criterion applies.
* `InverseGalois.CFT.Units.SIdeleNorm` assembles the local-to-global criterion for an idele that is
  a unit outside a finite invariant set of places to be a norm.  Over each orbit the sections form
  the module induced from the decomposition group of any one place, so a section is a norm as soon
  as its value at one place of each orbit is a local norm; and at a finite place outside the set
  nothing has to be assumed, because there the local subgroup is the units of the valuation ring and
  the decomposition group fixes a uniformizer.
* `InverseGalois.CFT.Approximation.Basic` proves weak approximation for an arbitrary finite family
  of nontrivial pairwise inequivalent absolute values on a field: the field, embedded diagonally in
  the product of its copies carrying the topologies of the members of the family, is dense.  The
  separation lemma of Artin and Whaples supplies, for each index, an element which the corresponding
  absolute value makes large and every other one makes small; the powers of that element weight a
  prescribed target so that the weight tends to one at its own index and to zero elsewhere, and the
  weighted sum of the targets converges to the target in every member of the family at once.
* `InverseGalois.CFT.Approximation.Places` checks the hypotheses for the places of a number field.
  Neither of two distinct primes contains the other, so an element of the first avoiding the second
  is small at the first and of absolute value one at the second; and a finite place makes every
  integer at most one whereas an infinite place makes two equal to two.  Weak approximation
  therefore applies to the family consisting of all the infinite places together with finitely many
  finite ones.
* `InverseGalois.CFT.Approximation.Completion` carries the statement over to the completions that
  the ideles are built from.  The completions add nothing, because the field is dense in each of
  them separately: a prescribed element of a completion is first replaced by an element of the field
  within half the required accuracy, the approximation is then carried out inside the field, and a
  triangle inequality combines the two.
* `InverseGalois.CFT.Local.PowClose` measures in the norm of a completion how close to a prescribed
  nonzero element another element has to be for the two to differ by an `n`-th power.  At a finite
  place the exponential turns a unit congruent to one to sufficient accuracy into an `n`-th power,
  and reading the valuation through the rank one homomorphism converts that accuracy into a bound
  on the norm; at an infinite place the completion is the reals or the complexes, and an element
  within distance one of one is a positive real or an arbitrary complex number.  The accuracy
  depends on the place and on the prescribed element but not on the element approximating it, so
  finitely many such conditions can be met at once.
* `InverseGalois.CFT.Approximation.PowClass` combines the two: every place supplies an accuracy
  within which an element of its completion differs from a prescribed nonzero one by an `n`-th
  power, and the smallest of the finitely many accuracies, cut down so as to keep the approximating
  element away from zero, is an accuracy at which weak approximation produces a single element of
  the field agreeing at every one of the places with the prescribed element up to an `n`-th power.
  In other words the field surjects onto the product over the chosen places of the quotients of the
  multiplicative groups of the completions by their `n`-th powers.
* `InverseGalois.CFT.Units.LocalPowIdele` reads that as a statement about the ideles.  The ideles
  whose component is an `n`-th power at every infinite place and at each of finitely many chosen
  finite places form a subgroup, and dividing an arbitrary idele by the element of the field that
  approximates it there lands in that subgroup, so the subgroup together with the principal ideles
  is everything.  This is the replacement, exact rather than merely dense, for the statement that
  the principal ideles together with the ideles trivial at the chosen places lie densely.
* `InverseGalois.CFT.Units.SplitOutside` puts the two halves together.  An idele of the base field
  that is a local power of exponent a multiple of the degree, at the infinite places and at the
  exceptional ones, is a local norm everywhere in a cyclic extension whose every other place splits
  completely: where the decomposition group is not already trivial its order divides the exponent,
  and a multiple of that order is a local norm.  Enlarging the support of the idele to a finite
  invariant set makes it an idele of a set of places, and the local-to-global criterion exhibits it
  as a norm.  So the norms and the principal ideles are everything, which the cyclic case of the
  first inequality forbids unless the extension is trivial; passing to a cyclic subextension gives
  the same conclusion for a solvable one.  This is the statement that an extension of number fields
  in which almost every place splits completely is trivial, in the form that leaves a finite set of
  places entirely unconstrained.
* `InverseGalois.CFT.Units.DecompositionOutside` runs the argument that the decomposition groups
  generate the Galois group against that sharper input.  Throwing away finitely many places of the
  base field, and all the infinite places, costs nothing: the decomposition groups at the finite
  places whose place below avoids a prescribed finite set already generate a solvable Galois group,
  because in the fixed field of the subgroup they generate every place of the base field outside the
  prescribed set splits completely.
* `InverseGalois.CFT.Units.FrobeniusPlace` identifies the decomposition group at a place of a Galois
  extension of number fields with the Galois group of the residue extension, over an arbitrary
  number field base.  The ring of integers upstairs is the ring of invariants of the ring of
  integers downstairs, the residue fields are finite and the residue extension separable, and the
  reduction map has the inertia group as its kernel.  At an unramified place the inertia group is
  trivial, so the decomposition group embeds in the Galois group of an extension of finite fields
  and is cyclic.
* `InverseGalois.CFT.Units.SplitPlaces` refines that generation statement to an intermediate field.
  For a Galois extension of prime exponent, the places away from a prescribed finite set whose
  decomposition group already fixes an intermediate field have decomposition groups generating
  exactly the subgroup fixing that field.  One inclusion is the definition; for the other, the
  decomposition groups of the extension over the intermediate field generate its Galois group, and
  at an unramified place the decomposition group over the base is cyclic of order one or the prime,
  so a nontrivial subgroup of it is everything.
* `InverseGalois.CFT.Units.GeneratingPrimes` cuts that generating family down to a basis indexed by
  places of the base field.  For a commutative Galois group the decomposition groups at two places
  above the same place of the base coincide, and at an unramified place the order divides the
  exponent, so greedily adjoining a decomposition group not already present multiplies the order of
  the subgroup generated by exactly the prime.  The outcome is a finite set of places of the base,
  disjoint from the prescribed set and splitting completely in the intermediate field, whose number
  of elements is the exponent of the prime in the degree over that field.
* `InverseGalois.CFT.Units.SplitPowIdele` names the subgroup of the ideles that the algebraic proof
  of the second inequality needs, cut out by two disjoint finite sets of finite places.  Nothing is
  asked at the infinite places nor at the places of the first set, an `n`-th power is asked at the
  places of the second, and a unit of the valuation ring everywhere else.  The first set carries the
  ideal classes and the ramification, so its places split completely and every local element there
  is a norm; at the places of the second set the local degree divides `n`; and outside the two sets
  the extension is unramified, so a local unit is a norm.  Those ideles together with the principal
  ones are everything: the first set carrying the ideal classes corrects a given idele into one that
  is a unit outside that set, and the `S`-units surjecting onto the local units modulo `n`-th powers
  at the places of the second set correct it further without disturbing anything outside the first.
* `InverseGalois.CFT.Units.SplitPowNorm` proves that those ideles really are norms from a cyclic
  extension with the expected local behaviour.  Only finitely many places lie above the two sets of
  places, so they form a finite invariant set of chosen places making the idele, read upstairs, an
  `S`-idele; at an infinite place and at a place above the first set the decomposition group is
  trivial, at a place above the second set the local component is an `n`-th power of a unit coming
  from the base field and the order of the decomposition group divides `n`, and outside the two sets
  the place is unramified and carries a uniformizer fixed by its decomposition group, so the
  local-to-global criterion applies.
* `InverseGalois.CFT.Local.UnitFiltration` sets up the two filtrations of a valued field: the
  additive one by the elements of small valuation, and the multiplicative one by the units
  congruent to one.  Subtracting one identifies a step of the unit filtration with the
  corresponding graded piece of the additive filtration.
* `InverseGalois.CFT.Local.FiltrationAction` records that a group acting on the field by isometries
  preserves both filtrations, so that subtracting one is a homomorphism of modules over the group
  and consecutive steps of the unit filtration sit in a short exact sequence with a graded piece of
  the additive filtration.
* `InverseGalois.CFT.Local.FiltrationFinite` deduces from the finiteness of every graded piece of
  the additive filtration that any two steps of either filtration are of finite relative index, the
  relative indices multiplying along a tower.
* `InverseGalois.CFT.Local.GradedFinite` reduces that hypothesis to a single graded piece: once the
  valuation takes the value just below one, multiplication by an element of that valuation shifts
  the additive filtration by one step, so all the graded pieces are isomorphic and finiteness of
  one of them gives finiteness of all.
* `InverseGalois.CFT.Local.UnitIndex` compares the two filtrations at their tops: reducing a unit
  of valuation one modulo the units congruent to one embeds the quotient of the unit group by a
  step of the unit filtration into a graded piece, so that step is of finite index in the unit
  group.
* `InverseGalois.CFT.Local.FiltrationHerbrand` shows that the Herbrand quotient of a step of the
  additive filtration does not depend on the step: consecutive steps are of finite index in one
  another, so the inclusion is an equivariant injection with finite cokernel.
* `InverseGalois.CFT.Local.TraceIntegral` records that a finite group acting faithfully by
  isometries makes the field a Galois extension of the subfield it fixes, every automorphism over
  which is again an isometry, so the trace of an element of the valuation ring lies in the
  valuation ring of the fixed field.
* `InverseGalois.CFT.Local.NormalLattice` uses the normal basis theorem to produce an element whose
  orbit is a basis over the fixed field.  The integral combinations of the orbit form a lattice
  inside a step of the additive filtration on which the group acts by translating the coefficients,
  and expanding an element in the dual basis for the trace form expresses its coefficients as
  traces, which are integral for a small enough element.  So the lattice contains a step of the
  filtration, and a cyclic group gives every step Herbrand quotient one.
* `InverseGalois.CFT.Local.ValuedTopology` records that a valued ring is nonarchimedean: every
  neighbourhood of zero contains an open, hence closed, subgroup.  So a step of the additive
  filtration contains every sum of its elements, and the valuation of an infinite sum is at most
  the largest valuation of a term.
* `InverseGalois.CFT.Local.NatValuation` computes the valuation of an integer in a valued field.
  An integer prime to the residue characteristic has valuation one, so the valuation of an
  arbitrary integer is that of the residue characteristic raised to its `p`-adic valuation, and
  Legendre's theorem bounds the valuation of a factorial.
* `InverseGalois.CFT.Local.Exp` constructs the exponential.  Legendre's bound makes the series
  converge on a small enough step of the additive filtration, the binomial theorem turns the Cauchy
  product into the addition formula, and the exponential of an element differs from one plus that
  element by one further step, so it changes no valuation and is injective.
* `InverseGalois.CFT.Local.ExpSurjective` shows that the exponential exhausts the corresponding
  step of the unit filtration: dividing a unit by the exponential of its difference from one gains
  a digit, and the exponential of the sum of the successive increments is the original unit.
* `InverseGalois.CFT.Local.ExpEquiv` packages this as an isomorphism between a deep enough step of
  the additive filtration and the corresponding step of the unit filtration.
* `InverseGalois.CFT.Local.ExpAction` makes that isomorphism equivariant: an isometric ring
  automorphism is continuous, hence commutes with infinite sums and with the exponential, so the
  two steps have the same Herbrand quotient.
* `InverseGalois.CFT.Local.UnitHerbrandChain` assembles the chain for a complete field with finite
  graded pieces: a deep enough step of the unit filtration inherits Herbrand quotient one from the
  additive filtration through the exponential, it is of finite index in the units of the valuation
  ring, and the valuation of a unit then gives the units of the field Herbrand quotient the order
  of the group.
* `InverseGalois.CFT.Local.TrivialIndex` runs the same chain with no action at all.  Multiplication
  by `n` moves a step of the additive filtration down by the valuation of `n`, so a step has
  Herbrand quotient the order of a graded piece raised to that valuation; the exponential, the
  finite index of a deep step, and the valuation sequence carry this to the units of the field,
  where an extra factor of `n` appears.  The index of the `n`-th powers in the units of the field
  is therefore `n`, times the order of the residue field raised to the valuation of `n`, times the
  number of `n`-th roots of unity.
* `InverseGalois.CFT.Local.UnramifiedUnits` sharpens that computation when the fixed field already
  contains a uniformizer: Hilbert's theorem 90 writes a unit whose conjugates multiply to one as a
  quotient, the uniformizer corrects the valuation of the representative, and the lower Tate group
  of the units of the valuation ring vanishes.  Their Herbrand quotient is one and both groups are
  finite, so the upper group vanishes as well.  Read through the definition of that group, the norm
  map on the units of the valuation ring is surjective onto the fixed ones.
* `InverseGalois.CFT.Local.PadicSquaresTwo` supplies the excluded prime: a dyadic unit is a square
  exactly when it is congruent to one modulo eight, and every nonzero dyadic number is a square
  times one of eight explicit representatives.
* `InverseGalois.CFT.Local.HilbertSymbol` defines the Hilbert symbol of two elements of a field as
  the isotropy of the form `z² - a x² - b y²`, establishes its symmetry, its invariance under
  squares and its interpretation as a norm from a quadratic extension, and computes it completely
  at the real place.
* `InverseGalois.CFT.Local.PadicHilbert` computes the Hilbert symbol of a `p`-adic field for odd
  `p`: two units are always isotropic, so the symbol is trivial whenever both valuations are even,
  and the symbol of `p` against a unit detects whether that unit is a square residue.
* `InverseGalois.CFT.Brauer.QuadraticExt` builds the quadratic extension obtained by adjoining a
  square root of a nonsquare, computes its norm form as `u² - b v²`, and identifies the relative
  Brauer group of that extension with the units modulo the values of the norm form.
* `InverseGalois.CFT.Brauer.Division` gives every central simple algebra its Wedderburn division
  representative, and deduces that the Brauer group of an algebraically closed field and of a
  finite field is trivial.
* `InverseGalois.CFT.Brauer.Quaternion` exhibits the first nontrivial Brauer classes: since `-1`
  is not a norm from `ℂ` to `ℝ`, nor from `ℚ(i)` to `ℚ`, the corresponding quaternion algebras are
  central simple algebras of dimension four that are not matrix algebras over the base field.
* `InverseGalois.CFT.Global.TernaryForms` restates the Hasse principle for an arbitrary diagonal
  ternary form over the rational field, and deduces the Hasse principle for the representation of
  a rational number by a diagonal binary form, in particular as a sum of two squares.
* `InverseGalois.CFT.Global.JacobiNonresidue` produces, for a squarefree integer other than one,
  arbitrarily large primes at which its Jacobi symbol is `-1`, by combining quadratic reciprocity
  with Dirichlet's theorem on primes in an arithmetic progression.
* `InverseGalois.CFT.Global.LocalSquares` deduces the Hasse principle for squares: a rational
  number that is a square in every field of `p`-adic numbers is a square, so the square classes of
  the rational field inject into the product of the local ones.
* `InverseGalois.CFT.Global.RationalSquareClasses` goes the other way, showing every square class
  of a `p`-adic field to contain a rational number, by approximating a `p`-adic number closely
  enough that the ratio is a square.
* `InverseGalois.CFT.Global.SquareClassApprox` upgrades that to weak approximation for square
  classes: a single rational number can be prescribed, up to squares, in finitely many `p`-adic
  fields at once, and its sign chosen freely.
* `InverseGalois.CFT.Global.OddValuation` computes the Hilbert symbol at an odd place of an
  integer prime to that place against an arbitrary argument, the answer depending only on the
  parity of the valuation and, when that parity is odd, on a Legendre symbol.
* `InverseGalois.CFT.Global.Existence` proves the first case of Serre's existence theorem: a
  family of prescribed local Hilbert symbols, trivial outside a set of places disjoint from the
  bad ones and satisfying the product formula, is realised by a single positive integer, produced
  by Dirichlet's theorem in an arithmetic progression.
* `InverseGalois.CFT.Global.ExistenceGeneral` removes the disjointness hypothesis by a twist,
  giving **Serre's existence theorem** in full: prescribed local Hilbert symbols subject only to
  the product formula are realised by a rational number.
* `InverseGalois.CFT.Global.ThreeSquaresOdd` shows that for an odd prime every `p`-adic number is
  a sum of three squares, the form `X² + Y² + Z²` being isotropic and therefore universal.
* `InverseGalois.CFT.Global.ThreeSquaresTwo` settles the dyadic case: a nonzero dyadic number is a
  sum of three squares exactly when its negative is not a square.
* `InverseGalois.CFT.Global.SevenModEight` translates that dyadic condition into arithmetic: the
  negative of a positive natural number is a dyadic square exactly when the number has the shape
  `4 ^ a * (8 * b + 7)`.
* `InverseGalois.CFT.Global.DavenportCassels` carries out the Davenport–Cassels descent for the
  sums of two and of three squares, so that a rational representation yields an integral one.
* `InverseGalois.CFT.Global.ThreeSquares` combines these into **the three-square theorem**: a
  natural number is a sum of three integer squares exactly when it is not of the shape
  `4 ^ a * (8 * b + 7)`.
* `InverseGalois.CFT.Global.QuaternaryForms` applies Serre's existence theorem to the **Hasse
  principle for diagonal forms in four variables**: such a form is isotropic exactly when its two
  halves share a nonzero value, and a common value at every place, the real place included, is
  the prescription of two families of Hilbert symbols whose product formula is reciprocity.
* `InverseGalois.CFT.Global.IntApprox` approximates a finite family of `p`-adic integers by a
  single rational integer, which may moreover be taken larger than any prescribed bound.
* `InverseGalois.CFT.Global.OddUnitIsotropy` records that a diagonal ternary form with unit
  coefficients over an odd `p`-adic field is isotropic, and that a nonzero rational is a unit at
  all but finitely many places.
* `InverseGalois.CFT.Global.QuinaryForms` proves the **Hasse principle for diagonal forms in five
  variables**: the binary and the ternary half share a value at every place, and the integer
  approximation produces a single rational value of the binary half lying in the right square
  class at each place where it matters, at which point the four-variable principle applies.
* `InverseGalois.CFT.Global.DiagForm` and `InverseGalois.CFT.Global.DiagSplit` set up a diagonal
  form in an arbitrary number of variables, indexed by a family of coefficients: an isotropic form
  with invertible coefficients is universal, its values are a union of square classes, and a form
  in at least three variables is isotropic exactly when its binary head and its tail represent a
  common nonzero value.
* `InverseGalois.CFT.Global.DiagBase` reads the principles in at most four variables in that
  language.
* `InverseGalois.CFT.Global.DiagHasse` proves the **Hasse principle for a diagonal form in an
  arbitrary number of variables** by induction on their number, the five-variable argument
  serving as the inductive step.
* `InverseGalois.CFT.Global.DiagRepr` frees that principle of its hypothesis on the coefficients
  and recasts it as a **Hasse principle for the representation of a prescribed rational number**
  by a diagonal form.
* `InverseGalois.CFT.Global.OddQuinary` shows that **a diagonal form in at least five variables is
  isotropic at every odd finite place** — among five valuations three share a parity, and the
  corresponding ternary subform is a unit form — so that the Hasse principle in five or more
  variables involves only the real and the dyadic place.
* `InverseGalois.CFT.Global.RealSigns` settles the real place: a diagonal real form is isotropic
  exactly when its coefficients are not all of one sign.  In at least five variables the Hasse
  principle therefore reads: **not all coefficients of one sign, and isotropic over `ℚ₂`**.
* `InverseGalois.CFT.Global.MatHasse` removes the restriction to diagonal forms: congruence of
  symmetric matrices preserves isotropy and commutes with base change, and every symmetric matrix
  over a field in which `2` is invertible is congruent to a diagonal one, whence the
  **Hasse principle for an arbitrary rational quadratic form** presented by a symmetric matrix.
* `InverseGalois.CFT.Local.DyadicQuinary` supplies the dyadic half of the count for unit
  coefficients: five dyadic units always admit a nontrivial zero of the diagonal form they define,
  because among five odd residues one can choose a subfamily whose sum, with the small square
  values `0`, `1` and `4`, is divisible by eight, leaving a coefficient congruent to one modulo
  eight and hence a square.  Together with the two preceding entries, **a diagonal rational form
  in at least five variables with odd integer coefficients is isotropic exactly when its
  coefficients are not all of one sign**.
* `InverseGalois.CFT.Local.DyadicNondegenerate` completes the dyadic Hilbert symbol in the way the
  odd places were already completed: against a fixed dyadic nonsquare the symbol takes the value
  `-1`, so it is a surjection onto the units of the integers, the norm subgroup of a quadratic
  extension of the dyadic numbers has index two, and the relative Brauer group of such an
  extension has order two.
* `InverseGalois.CFT.Local.DyadicQuaternary` supplies the companion count in four variables: a
  diagonal dyadic form with three unit coefficients and one coefficient of valuation one is
  isotropic, again by a search modulo eight.
* `InverseGalois.CFT.Global.DiagScale` records that isotropy of a diagonal form is unchanged when
  the coefficients are multiplied by nonzero squares or by a common nonzero scalar, and that every
  nonzero dyadic number becomes, after multiplication by a square, a unit or twice a unit.
* `InverseGalois.CFT.Global.Meyer` removes the hypothesis on the coefficients altogether.  Among
  five coefficients, normalised to be units or twice units, either all five are of one kind — the
  quinary unit form, after dividing the whole form by two in the second case — or three are of one
  kind and a fourth of the other, which is the quaternary form; so **a diagonal form over the
  dyadic numbers in at least five variables is isotropic**, the last place at which anything could
  have obstructed it.  With the real and the odd places this is **Meyer's theorem**: a diagonal
  rational form in at least five variables is isotropic exactly when it is indefinite, and it then
  represents every rational number the real place allows.
* `InverseGalois.CFT.Local.DyadicAnisotropic` shows that five variables are genuinely needed: the
  sum of four squares, the norm form of the Hamilton quaternions, has no nontrivial dyadic zero,
  because scaling by a coordinate of largest absolute value and reducing modulo eight leaves four
  residues, one of them one, whose squares would have to sum to zero.  **The `u`-invariant of the
  dyadic numbers is exactly four.**
* `InverseGalois.CFT.Local.OddAnisotropic` does the same at an odd place, where the obstruction is
  a valuation rather than a congruence: the quaternary form built from the norm form of the
  unramified quadratic extension and its multiple by the uniformiser would equate a value of that
  norm form with the uniformiser times another such value, and the values of the norm form all
  have even valuation.  **The `u`-invariant of a field of `p`-adic numbers is exactly four.**
* `InverseGalois.CFT.Local.DyadicNormFive` records what this costs the Hasse principle in four
  variables.  The form `⟨1, -5, -2, 10⟩` is the norm form of the unramified quadratic extension of
  the dyadic numbers together with its multiple by the uniformiser, so it is anisotropic there and
  hence over the rational numbers; but its coefficients have both signs, so it is isotropic over
  the real numbers.  **In four variables the real place alone does not decide isotropy**, and
  Meyer's five-variable hypothesis cannot be weakened.
* `InverseGalois.CFT.Local.PadicLocalField` records that a field of `p`-adic numbers is a
  nonarchimedean local field in the sense of the valuative formalism: its norm is compatible with
  its valuative relation, its topology is the valuative one, and its ring of integers is the ring
  of `p`-adic integers, a compact complete discrete valuation ring with finite residue field.
* `InverseGalois.CFT.GroupCohomology.CyclicH1` is the cohomological form of Hilbert's theorem 90 for
  an abstract finite cyclic group.  A `1`-cocycle is determined by its value at a generator, because
  the cocycle relation propagates that value along the powers of the generator; the value therefore
  lies in the kernel of the norm operator, and the cocycle is a coboundary as soon as that value is
  in the image of the generator minus one.  So the first cohomology vanishes whenever the kernel of
  the norm operator is the image of the generator minus one.
* `InverseGalois.CFT.Units.IdeleRep` assembles the Galois actions on the units, on the ideles and on
  the idele classes into `ℤ`-linear representations of the whole Galois group, which is the shape
  the machinery of group cohomology wants; an action by additive automorphisms is a representation
  because an additive map is automatically `ℤ`-linear.  Enlarging the base field leaves the action
  untouched, because an automorphism acts through its underlying map of fields.
* `InverseGalois.CFT.Units.IdeleClassH1` reads the first inequality and the Herbrand quotient of the
  idele classes as the vanishing of the first cohomology of a cyclic extension.  The group `Ĥ⁻¹` of
  the idele classes is trivial because the Herbrand quotient and the order of `Ĥ⁰` are both the
  degree, and the norm operator of the representation is the Tate norm operator of a generator, so
  the two statements match up.
* `InverseGalois.CFT.GroupCohomology.H1Transport` provides the two dévissage tools for the first
  cohomology at the level of cocycles: an isomorphism of groups compatible with an isomorphism of
  modules carries vanishing across, and a surjection of groups whose kernel acts trivially on a
  submodule that is exactly the invariants of the kernel lets the vanishing be assembled from the
  quotient and the kernel.
* `InverseGalois.CFT.Units.IdeleClassComap` puts the idele classes of a subfield inside the idele
  classes of a Galois extension.  The map is injective because a unit fixed by the whole Galois
  group is a unit of the subfield, and its image is exactly the part fixed by the Galois group over
  the subfield, because a fixed class is the class of a fixed idele and a fixed idele comes from the
  subfield.  Fixing a class rather than an idele needs Hilbert's theorem 90 for the whole group,
  which is proved alongside it in `InverseGalois.CFT.Units.IdeleClassFixed`.
* `InverseGalois.CFT.Units.IdeleClassTower` is the dévissage of the first cohomology of the idele
  class group along a tower: the vanishing over the middle field and the vanishing of the top over
  the middle give the vanishing of the top over the base.
* `InverseGalois.CFT.GroupCohomology.SylowRes` reduces the vanishing of a positive-degree cohomology
  class of a finite group to its vanishing on subgroups of index prime to each prime dividing the
  order, by playing the annihilation by the order against the annihilation by the index that
  restriction and corestriction provide.
* `InverseGalois.CFT.Units.IdeleClassH1Full` removes the cyclicity hypothesis altogether.  A group
  of prime-power order has a normal subgroup of prime index, so the tower dévissage and induction on
  the exponent settle every extension of prime-power degree; and restriction to a Sylow subgroup is
  the cohomology over its fixed field, whose degree is a prime power.  **The first cohomology of the
  idele class group of an arbitrary Galois extension of number fields vanishes.**
* `InverseGalois.CFT.Units.IdeleClassSES` assembles the units, the ideles and the idele classes into
  a short exact sequence of representations of the Galois group.  Its long exact cohomology sequence
  starts at the first cohomology of the idele classes, which has just been shown to vanish, so **the
  second cohomology of the units injects into the second cohomology of the ideles** — the global
  half of the Albert-Brauer-Hasse-Noether theorem.
* `InverseGalois.CFT.GroupCohomology.CyclicCoboundary` turns the Herbrand description of the second
  cohomology of a finite cyclic group into the concrete statement the local half needs: if every
  invariant element is a norm then every two-cocycle is a coboundary, with an explicit one-cochain.
  The statement is given for an action by group automorphisms and, through the multiplicative copy
  of an additive group, for an action by additive automorphisms, where the sum over the group may
  be replaced by the geometric sum of the powers of a generator.
* `InverseGalois.CFT.Local.UnramifiedCoboundary` runs that criterion at an unramified place.  The
  decomposition group there is cyclic and the completion has a uniformizer it fixes, so the norms of
  the units of the valuation ring exhaust the fixed ones, and **every two-cocycle of the
  decomposition group with values in those units is a coboundary**.
* `InverseGalois.CFT.Units.IdeleCoboundary` globalises that: a two-cocycle with values in the ideles
  which is a coboundary at every place is a coboundary.  The coordinates in a Galois orbit determine
  one another, so a local one-cochain at each place assembles into a global one; at all but the
  finitely many places which are ramified or where the cocycle is not a unit, the local cochain may
  be chosen with values in the units of the valuation ring, and the assembled family is an idele.
* `InverseGalois.CFT.GroupCohomology.MapCoboundary` records the elementary fact that a map of
  representations which is injective on second cohomology reflects coboundaries, which is how an
  injectivity statement coming from a long exact sequence gets applied to an explicit cocycle.
* `InverseGalois.CFT.Units.ABHN` combines the two halves.  The second cohomology of the units
  injects into the second cohomology of the ideles, and a two-cocycle of the ideles which is locally
  a coboundary is a coboundary, so **a two-cocycle with values in the units of the top field which
  is a coboundary at every place is a coboundary** — the Albert-Brauer-Hasse-Noether theorem in the
  shape of the vanishing of the second Tate-Shafarevich group of the units.
* `InverseGalois.CFT.Kummer.InflationRootsOfUnity` turns a statement about the units back into one
  about the roots of unity.  If a two-cocycle whose values are `n`-th roots of unity is a coboundary
  in the units, then the `n`-th powers of the cochain witnessing that form a one-cocycle, so
  Hilbert's theorem 90 writes them as the coboundary of a single element; over an extension
  containing an `n`-th root of that element the inflated cocycle is cobounded by a cochain whose
  values are again `n`-th roots of unity.
* `InverseGalois.CFT.GroupCohomology.CoprimeSplit` descends the resulting statement from the
  cyclotomic field back to the base field.  A central extension of finite groups which admits a
  section homomorphism over a subgroup whose index is coprime to the order of the kernel admits a
  section homomorphism outright: the transfer of the difference between the identity and the given
  section is the power map on the kernel, and inverting that power map turns it into a retraction.
* `InverseGalois.CFT.GroupCohomology.CoprimeCoboundary` supplies the local hypotheses of the
  Albert-Brauer-Hasse-Noether theorem at the places where they are free of arithmetic.  Summing the
  cocycle identity over the third variable exhibits the order of the group times a two-cocycle as a
  coboundary, so **a two-cocycle killed by an integer coprime to the order of the group is a
  coboundary**; at an archimedean place of a `p`-extension with `p` odd the decomposition group has
  order at most two and the hypothesis is automatic.
* `InverseGalois.CFT.Units.ABHNTorsion` spends that observation, together with the vanishing at an
  unramified finite place, on the local hypotheses of the Albert-Brauer-Hasse-Noether theorem.  A
  unit killed by a nonzero integer has valuation zero, so at an unramified place the local component
  of the cocycle is a two-cocycle of the cyclic decomposition group with values in the units of the
  valuation ring; at an archimedean place the decomposition group has order one or two.  Hence **a
  two-cocycle of the units killed by an odd integer which is a coboundary at every ramified finite
  place is a coboundary**, which is the form in which the theorem meets a central embedding problem
  with kernel of odd prime order.
* `InverseGalois.CFT.Kummer.RadicalClosure` provides the field over which the descent from the units
  to the roots of unity takes place.  A finite extension inside an algebraic closure is contained in
  a finite normal extension containing an `n`-th root of each of finitely many prescribed elements:
  the roots exist in the algebraic closure and are algebraic over the base, so adjoining them and
  passing to the normal closure keeps the extension finite.
* `InverseGalois.CFT.GroupCohomology.CentralLift` is the group-theoretic engine which spends a
  coboundary statement on an embedding problem.  A set-theoretic section of a surjection with
  central kernel has a factor set measuring its failure to be a homomorphism, and that factor set is
  a two-cocycle for the trivial action; if the cocycle pulled back along a homomorphism is a
  coboundary, then correcting the section by the cochain produces **a homomorphic lift of that
  homomorphism**, and when the kernel lies inside the Frattini subgroup the lift is automatically
  surjective, so it solves the embedding problem properly.
* `InverseGalois.CFT.Kummer.RootsInBase` matches the two sides of that exchange.  A field containing
  a primitive `n`-th root of unity already contains every `n`-th root of unity of every extension,
  because the image of the primitive root is still primitive; hence the Galois group acts trivially
  on them, and **a cyclic group of order `n` embeds onto them**, which is how a cochain of roots of
  unity produced by Kummer theory is read as a cochain with values in the kernel of a central
  extension of order `n`.
-/
