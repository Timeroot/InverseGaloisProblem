import InverseGalois.CFT.Approximation.Basic
import InverseGalois.CFT.Approximation.Completion
import InverseGalois.CFT.Approximation.Places
import InverseGalois.CFT.Approximation.PowClass
import InverseGalois.CFT.Brauer.AdicUnramified
import InverseGalois.CFT.Brauer.BaseChange
import InverseGalois.CFT.Brauer.BaseChangeCentralizer
import InverseGalois.CFT.Brauer.Centralizer
import InverseGalois.CFT.Brauer.CentralizerProduct
import InverseGalois.CFT.Brauer.CrossedProduct
import InverseGalois.CFT.Brauer.CrossedProductCohomologous
import InverseGalois.CFT.Brauer.CrossedProductCompositum
import InverseGalois.CFT.Brauer.CrossedProductMul
import InverseGalois.CFT.Brauer.CrossedProductRecognition
import InverseGalois.CFT.Brauer.CrossedProductRestrict
import InverseGalois.CFT.Brauer.CrossedProductSimple
import InverseGalois.CFT.Brauer.CrossedProductSplit
import InverseGalois.CFT.Brauer.CrossedProductSplitting
import InverseGalois.CFT.Brauer.CyclicAlgebra
import InverseGalois.CFT.Brauer.CyclicBaseChange
import InverseGalois.CFT.Brauer.CyclicBrauer
import InverseGalois.CFT.Brauer.CyclicCompositum
import InverseGalois.CFT.Brauer.CyclicInvariant
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Brauer.CyclicTower
import InverseGalois.CFT.Brauer.Division
import InverseGalois.CFT.Brauer.DivisionAbsValue
import InverseGalois.CFT.Brauer.DivisionCompact
import InverseGalois.CFT.Brauer.DivisionCyclic
import InverseGalois.CFT.Brauer.DivisionGalois
import InverseGalois.CFT.Brauer.DivisionInteger
import InverseGalois.CFT.Brauer.DivisionMaximal
import InverseGalois.CFT.Brauer.DivisionNorm
import InverseGalois.CFT.Brauer.DivisionResidue
import InverseGalois.CFT.Brauer.DivisionResidueBase
import InverseGalois.CFT.Brauer.DivisionSplitting
import InverseGalois.CFT.Brauer.DivisionTeichmuller
import InverseGalois.CFT.Brauer.DivisionValueGroup
import InverseGalois.CFT.Brauer.Exponent
import InverseGalois.CFT.Brauer.Frobenius
import InverseGalois.CFT.Brauer.FrobeniusBaseChange
import InverseGalois.CFT.Brauer.FrobeniusRamified
import InverseGalois.CFT.Brauer.FrobeniusTower
import InverseGalois.CFT.Brauer.GaloisSplitting
import InverseGalois.CFT.Brauer.Group
import InverseGalois.CFT.Brauer.H2Brauer
import InverseGalois.CFT.Brauer.H2Surjective
import InverseGalois.CFT.Brauer.InertiaSubfield
import InverseGalois.CFT.Brauer.InvariantBaseChange
import InverseGalois.CFT.Brauer.InvariantBaseUnramified
import InverseGalois.CFT.Brauer.InvariantCompositum
import InverseGalois.CFT.Brauer.InvariantInjective
import InverseGalois.CFT.Brauer.InvariantMap
import InverseGalois.CFT.Brauer.InvariantRamified
import InverseGalois.CFT.Brauer.InvariantRestrict
import InverseGalois.CFT.Brauer.InvariantSurjective
import InverseGalois.CFT.Brauer.Kernel
import InverseGalois.CFT.Brauer.LocalBrauerBound
import InverseGalois.CFT.Brauer.LocalBrauerOrder
import InverseGalois.CFT.Brauer.LocalInvariant
import InverseGalois.CFT.Brauer.LocalInvariantRestrict
import InverseGalois.CFT.Brauer.LocalReciprocity
import InverseGalois.CFT.Brauer.LocalUnramified
import InverseGalois.CFT.Brauer.MaximalSubfield
import InverseGalois.CFT.Brauer.Opposite
import InverseGalois.CFT.Brauer.Primary
import InverseGalois.CFT.Brauer.QuadraticExt
import InverseGalois.CFT.Brauer.Quaternion
import InverseGalois.CFT.Brauer.RamificationIdentity
import InverseGalois.CFT.Brauer.RationalBrauer
import InverseGalois.CFT.Brauer.RelativeIndex
import InverseGalois.CFT.Brauer.RelativeTorsion
import InverseGalois.CFT.Brauer.RealBrauer
import InverseGalois.CFT.Brauer.RealInvariant
import InverseGalois.CFT.Brauer.RealPlace
import InverseGalois.CFT.Brauer.ResidueBaseChange
import InverseGalois.CFT.Brauer.ResidueDegree
import InverseGalois.CFT.Brauer.ResidueGalois
import InverseGalois.CFT.Brauer.Semilinear
import InverseGalois.CFT.Brauer.SkolemNoether
import InverseGalois.CFT.Brauer.SolvableBound
import InverseGalois.CFT.Brauer.SolvableNormBound
import InverseGalois.CFT.Brauer.Split
import InverseGalois.CFT.Brauer.SplittingSubfield
import InverseGalois.CFT.Brauer.TensorSimple
import InverseGalois.CFT.Brauer.Tower
import InverseGalois.CFT.Brauer.UnramifiedAdjoin
import InverseGalois.CFT.Brauer.UnramifiedAut
import InverseGalois.CFT.Brauer.UnramifiedClassOrder
import InverseGalois.CFT.Brauer.UnramifiedCompositum
import InverseGalois.CFT.Brauer.UnramifiedDegree
import InverseGalois.CFT.Brauer.UnramifiedRelative
import InverseGalois.CFT.CentralCompositum
import InverseGalois.CFT.CharacterSpan
import InverseGalois.CFT.Compositum
import InverseGalois.CFT.CompositumBase
import InverseGalois.CFT.CompositumLift
import InverseGalois.CFT.CutField
import InverseGalois.CFT.Cyclotomic.BuildingBlock
import InverseGalois.CFT.Cyclotomic.Chebotarev
import InverseGalois.CFT.Cyclotomic.CyclicSubfield
import InverseGalois.CFT.Cyclotomic.CyclotomicInertiaDeg
import InverseGalois.CFT.Cyclotomic.DivisorSubfield
import InverseGalois.CFT.Cyclotomic.EighthRootSubfield
import InverseGalois.CFT.Cyclotomic.Frobenius
import InverseGalois.CFT.Cyclotomic.FrobeniusSplitting
import InverseGalois.CFT.Cyclotomic.InertiaOrder
import InverseGalois.CFT.Cyclotomic.OnePrimeRamified
import InverseGalois.CFT.Cyclotomic.PrimeSelection
import InverseGalois.CFT.Cyclotomic.QuadraticSubfield
import InverseGalois.CFT.Cyclotomic.Ramified
import InverseGalois.CFT.Cyclotomic.Splitting
import InverseGalois.CFT.Cyclotomic.SquareRoots
import InverseGalois.CFT.Cyclotomic.TotallyRamified
import InverseGalois.CFT.Cyclotomic.TotallyRealSubfield
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Decomposition
import InverseGalois.CFT.Disjoint
import InverseGalois.CFT.FibreCompositum
import InverseGalois.CFT.FrobeniusInvolution
import InverseGalois.CFT.FrobeniusStabilizer
import InverseGalois.CFT.GaloisDescent
import InverseGalois.CFT.GroupCohomology.Classification
import InverseGalois.CFT.GroupCohomology.CentralLift
import InverseGalois.CFT.GroupCohomology.CentralTwist
import InverseGalois.CFT.GroupCohomology.Cohomologous
import InverseGalois.CFT.GroupCohomology.CoboundaryDescent
import InverseGalois.CFT.GroupCohomology.CoprimeCoboundary
import InverseGalois.CFT.GroupCohomology.CoprimeDescent
import InverseGalois.CFT.GroupCohomology.CoprimeSplit
import InverseGalois.CFT.GroupCohomology.Corestriction
import InverseGalois.CFT.GroupCohomology.Cup
import InverseGalois.CFT.GroupCohomology.Cyclic
import InverseGalois.CFT.GroupCohomology.CyclicRestrict
import InverseGalois.CFT.GroupCohomology.CyclicH1
import InverseGalois.CFT.GroupCohomology.CyclicCoboundary
import InverseGalois.CFT.GroupCohomology.CyclicH2
import InverseGalois.CFT.GroupCohomology.CyclicSubgroup
import InverseGalois.CFT.GroupCohomology.CyclicTate
import InverseGalois.CFT.GroupCohomology.CyclicTateMap
import InverseGalois.CFT.GroupCohomology.CyclicSurjective
import InverseGalois.CFT.GroupCohomology.DisjointFundamental
import InverseGalois.CFT.GroupCohomology.Duality
import InverseGalois.CFT.GroupCohomology.ExtensionMap
import InverseGalois.CFT.GroupCohomology.Pullback
import InverseGalois.CFT.GroupCohomology.H1Transport
import InverseGalois.CFT.GroupCohomology.H2Devissage
import InverseGalois.CFT.GroupCohomology.H2Sylow
import InverseGalois.CFT.GroupCohomology.H2Transport
import InverseGalois.CFT.GroupCohomology.IndexTwo
import InverseGalois.CFT.GroupCohomology.InfResTwo
import InverseGalois.CFT.GroupCohomology.InfResTwoInjective
import InverseGalois.CFT.GroupCohomology.Inflation
import InverseGalois.CFT.GroupCohomology.InflationOrder
import InverseGalois.CFT.GroupCohomology.InflationRestriction
import InverseGalois.CFT.GroupCohomology.MapCoboundary
import InverseGalois.CFT.GroupCohomology.OfCocycle
import InverseGalois.CFT.GroupCohomology.SylowRes
import InverseGalois.CFT.GroupCohomology.TateTwist
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
import InverseGalois.CFT.Global.NegOneSymbol
import InverseGalois.CFT.Global.OddUnitIsotropy
import InverseGalois.CFT.Global.QuaternaryForms
import InverseGalois.CFT.Global.QuinaryForms
import InverseGalois.CFT.Global.RealSigns
import InverseGalois.CFT.Global.RationalSquareClasses
import InverseGalois.CFT.Global.Reciprocity
import InverseGalois.CFT.Global.ReciprocityOmit
import InverseGalois.CFT.Global.SevenModEight
import InverseGalois.CFT.Global.SquareClassApprox
import InverseGalois.CFT.Global.SquarefreeCRT
import InverseGalois.CFT.Global.TernaryForms
import InverseGalois.CFT.Global.ThreeSquares
import InverseGalois.CFT.Global.ThreeSquaresOdd
import InverseGalois.CFT.Global.ThreeSquaresTwo
import InverseGalois.CFT.Global.TwoGenerators
import InverseGalois.CFT.GrunwaldWang
import InverseGalois.CFT.Herbrand
import InverseGalois.CFT.InertiaAbelian
import InverseGalois.CFT.InertiaFixedField
import InverseGalois.CFT.InertiaGeneration
import InverseGalois.CFT.InertiaRestrict
import InverseGalois.CFT.InertiaSubgroup
import InverseGalois.CFT.InertiaSurjective
import InverseGalois.CFT.InertiaTransport
import InverseGalois.CFT.KerField
import InverseGalois.CFT.KroneckerWeber
import InverseGalois.CFT.Kummer.CentralEmbedding
import InverseGalois.CFT.Kummer.CentralEmbeddingPlaces
import InverseGalois.CFT.Kummer.CentralEmbeddingSqrtNegOne
import InverseGalois.CFT.Kummer.CocycleDescent
import InverseGalois.CFT.Kummer.CongruentRadical
import InverseGalois.CFT.Kummer.CyclicIndex
import InverseGalois.CFT.Kummer.CyclotomicDescent
import InverseGalois.CFT.Kummer.CyclotomicPlace
import InverseGalois.CFT.Kummer.Denominator
import InverseGalois.CFT.Kummer.DyadicInertiaChar
import InverseGalois.CFT.Kummer.DyadicPlace
import InverseGalois.CFT.Kummer.DyadicSquareClass
import InverseGalois.CFT.Kummer.GlobalPower
import InverseGalois.CFT.Kummer.InertiaBound
import InverseGalois.CFT.Kummer.InflationRootsOfUnity
import InverseGalois.CFT.Kummer.LevelOne
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.Kummer.LocalSurjective
import InverseGalois.CFT.Kummer.Pairing
import InverseGalois.CFT.Kummer.PowBasis
import InverseGalois.CFT.Kummer.PowIndex
import InverseGalois.CFT.Kummer.PowerCriterion
import InverseGalois.CFT.Kummer.QuadraticChar
import InverseGalois.CFT.Kummer.QuadraticGenerator
import InverseGalois.CFT.Kummer.RadicalCharacter
import InverseGalois.CFT.Kummer.RadicalClosure
import InverseGalois.CFT.Kummer.RadicandLevel
import InverseGalois.CFT.Kummer.RamifiedCyclotomicPlace
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
import InverseGalois.CFT.Local.AdicLocalField
import InverseGalois.CFT.Local.AdicPowIndex
import InverseGalois.CFT.Local.AdicResidue
import InverseGalois.CFT.Local.AdicUnits
import InverseGalois.CFT.Local.AdicUnramified
import InverseGalois.CFT.Local.ComplexHerbrand
import InverseGalois.CFT.Local.CompleteNormIndex
import InverseGalois.CFT.Local.CyclicNormIndex
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
import InverseGalois.CFT.Local.FixedFieldValued
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
import InverseGalois.CFT.Local.KummerNonNorm
import InverseGalois.CFT.Local.LegendreHilbert
import InverseGalois.CFT.Local.NormIndex
import InverseGalois.CFT.Local.NormValued
import InverseGalois.CFT.Local.NormalLattice
import InverseGalois.CFT.Local.OddAnisotropic
import InverseGalois.CFT.Local.PadicHilbert
import InverseGalois.CFT.Local.PadicHilbertMul
import InverseGalois.CFT.Local.PadicLocalField
import InverseGalois.CFT.Local.PadicSquares
import InverseGalois.CFT.Local.NatValuation
import InverseGalois.CFT.Local.PadicSquaresTwo
import InverseGalois.CFT.Local.PowClose
import InverseGalois.CFT.Local.PrimeResidue
import InverseGalois.CFT.Local.PrimeResidueField
import InverseGalois.CFT.Local.PowNeighbourhood
import InverseGalois.CFT.Local.RamifiedNormForm
import InverseGalois.CFT.Local.RootOfUnityValued
import InverseGalois.CFT.Local.SpectralNorm
import InverseGalois.CFT.Local.TraceIntegral
import InverseGalois.CFT.Local.TrivialIndex
import InverseGalois.CFT.Local.SubfieldValued
import InverseGalois.CFT.Local.UnitFiltration
import InverseGalois.CFT.Local.UnitHerbrandChain
import InverseGalois.CFT.Local.UnitIndex
import InverseGalois.CFT.Local.UnitPowIndex
import InverseGalois.CFT.Local.UnitPowRoot
import InverseGalois.CFT.Local.UnitRootPower
import InverseGalois.CFT.Local.UnitValuation
import InverseGalois.CFT.Local.UnramifiedCoboundary
import InverseGalois.CFT.Local.UnramifiedInvariant
import InverseGalois.CFT.Local.UnramifiedNormForm
import InverseGalois.CFT.Local.UnramifiedNormValue
import InverseGalois.CFT.Local.UnramifiedUnits
import InverseGalois.CFT.Local.ValuedTopology
import InverseGalois.CFT.Multiquadratic
import InverseGalois.CFT.NilpotentCompositum
import InverseGalois.CFT.NilpotentQuotient
import InverseGalois.CFT.NormSubgroup
import InverseGalois.CFT.PGroupCompositum
import InverseGalois.CFT.PairwiseResidue
import InverseGalois.CFT.PiDual
import InverseGalois.CFT.PiIndex
import InverseGalois.CFT.PrimeProductSquare
import InverseGalois.CFT.Profinite.Cochain
import InverseGalois.CFT.Profinite.Comap
import InverseGalois.CFT.Profinite.Cup
import InverseGalois.CFT.Profinite.Hilbert90
import InverseGalois.CFT.Profinite.InfRes
import InverseGalois.CFT.Profinite.Kummer
import InverseGalois.CFT.Profinite.Quotient
import InverseGalois.CFT.Profinite.Krull
import InverseGalois.CFT.Profinite.Res
import InverseGalois.CFT.Profinite.Trivial
import InverseGalois.CFT.RelativeFrobenius
import InverseGalois.CFT.RestrictLE
import InverseGalois.CFT.ScalarSemidirect
import InverseGalois.CFT.Scholz.AbelianInertia
import InverseGalois.CFT.Scholz.AbelianInertiaTransport
import InverseGalois.CFT.Scholz.BlockDefect
import InverseGalois.CFT.Scholz.BlockGenerators
import InverseGalois.CFT.Scholz.BlockInertia
import InverseGalois.CFT.Scholz.BlockRealization
import InverseGalois.CFT.Scholz.AuxPrimeChoice
import InverseGalois.CFT.Scholz.AuxPrimeField
import InverseGalois.CFT.Scholz.BadPrimes
import InverseGalois.CFT.Scholz.BaseChange
import InverseGalois.CFT.Scholz.BaseDescent
import InverseGalois.CFT.Scholz.CentralCyclicLift
import InverseGalois.CFT.Scholz.CentralStep
import InverseGalois.CFT.Scholz.CanonicalDefect
import InverseGalois.CFT.Scholz.CentralDefect
import InverseGalois.CFT.Scholz.CentralStepTwo
import InverseGalois.CFT.Scholz.ClassStepData
import InverseGalois.CFT.Scholz.CompositumTransport
import InverseGalois.CFT.Scholz.Condition
import InverseGalois.CFT.Scholz.CorrectingCharacter
import InverseGalois.CFT.Scholz.CorrectingSubfield
import InverseGalois.CFT.Scholz.CoverInertia
import InverseGalois.CFT.Scholz.CoverObstruction
import InverseGalois.CFT.Scholz.CyclicSupplement
import InverseGalois.CFT.Scholz.DecompositionLift
import InverseGalois.CFT.Scholz.DyadicClassStep
import InverseGalois.CFT.Scholz.DyadicCorrector
import InverseGalois.CFT.Scholz.DyadicInduction
import InverseGalois.CFT.Scholz.DyadicInitialStage
import InverseGalois.CFT.Scholz.DyadicLiftCorrection
import InverseGalois.CFT.Scholz.DyadicRadical
import InverseGalois.CFT.Scholz.DyadicResidueCorrection
import InverseGalois.CFT.Scholz.DyadicResidueDegree
import InverseGalois.CFT.Scholz.DyadicShrink
import InverseGalois.CFT.Scholz.DyadicSocle
import InverseGalois.CFT.Scholz.DyadicStage
import InverseGalois.CFT.Scholz.DyadicStageTransition
import InverseGalois.CFT.Scholz.DyadicStepUp
import InverseGalois.CFT.Scholz.ElementaryAbelianSolutionTwo
import InverseGalois.CFT.Scholz.FixedFieldRamification
import InverseGalois.CFT.Scholz.FrattiniInertia
import InverseGalois.CFT.Scholz.FrattiniInertiaBound
import InverseGalois.CFT.Scholz.FrattiniInertiaSmall
import InverseGalois.CFT.Scholz.FrattiniSolution
import InverseGalois.CFT.Scholz.FrattiniStep
import InverseGalois.CFT.Scholz.FrobeniusDefect
import InverseGalois.CFT.Scholz.FrobeniusSymbol
import InverseGalois.CFT.Scholz.Induction
import InverseGalois.CFT.Scholz.InertSubfield
import InverseGalois.CFT.Scholz.InertiaRankOne
import InverseGalois.CFT.Scholz.InertiaTwist
import InverseGalois.CFT.Scholz.LocalTransport
import InverseGalois.CFT.Scholz.MultiquadraticBase
import InverseGalois.CFT.Scholz.MultiquadraticSqrt
import InverseGalois.CFT.Scholz.NilpotentOdd
import InverseGalois.CFT.Scholz.NilpotentRadical
import InverseGalois.CFT.Scholz.NilpotentSylowTwo
import InverseGalois.CFT.Scholz.PGroupInertia
import InverseGalois.CFT.Scholz.PGroupSolution
import InverseGalois.CFT.Scholz.PowerResidue
import InverseGalois.CFT.Scholz.PrimeChoice
import InverseGalois.CFT.Scholz.PrimeIndependence
import InverseGalois.CFT.Scholz.PrimeOrderInertia
import InverseGalois.CFT.Scholz.ProperSolution
import InverseGalois.CFT.Scholz.ProperSolutionTwo
import InverseGalois.CFT.Scholz.RadicalDisjoint
import InverseGalois.CFT.Scholz.RadicalSplitting
import InverseGalois.CFT.Scholz.RadicalTower
import InverseGalois.CFT.Scholz.RamificationControl
import InverseGalois.CFT.Scholz.Realization
import InverseGalois.CFT.Scholz.ResidueCorrection
import InverseGalois.CFT.Scholz.ResidueSpan
import InverseGalois.CFT.Scholz.ResidueSymbol
import InverseGalois.CFT.Scholz.Selector
import InverseGalois.CFT.Scholz.SplitCase
import InverseGalois.CFT.Scholz.SplitInertiaAt
import InverseGalois.CFT.Scholz.SplitInertiaTower
import InverseGalois.CFT.Scholz.SplitReduction
import InverseGalois.CFT.Scholz.SplitStep
import InverseGalois.CFT.Scholz.StepRamification
import InverseGalois.CFT.Scholz.StepSqrt
import InverseGalois.CFT.Scholz.StrongScholz
import InverseGalois.CFT.Scholz.SubfieldScholz
import InverseGalois.CFT.Scholz.Tame
import InverseGalois.CFT.Scholz.Twist
import InverseGalois.CFT.Scholz.TwistStep
import InverseGalois.CFT.Scholz.UnramifiedFactorInertia
import InverseGalois.CFT.Scholz.UnramifiedSolution
import InverseGalois.CFT.Scholz.UnramifiedSolutionTwo
import InverseGalois.CFT.SplitCompositum
import InverseGalois.CFT.SplitInertiaPrime
import InverseGalois.CFT.SplitSup
import InverseGalois.CFT.SqrtCompositum
import InverseGalois.CFT.SqrtCompositumDisjoint
import InverseGalois.CFT.SqrtFrattini
import InverseGalois.CFT.SqrtNegOne
import InverseGalois.CFT.SqrtRamification
import InverseGalois.CFT.SqrtSign
import InverseGalois.CFT.SqrtUnramified
import InverseGalois.CFT.SquareClasses
import InverseGalois.CFT.SubgroupCounting
import InverseGalois.CFT.SubgroupHilbert90
import InverseGalois.CFT.SubgroupIndex
import InverseGalois.CFT.TameCharacter
import InverseGalois.CFT.TameCyclic
import InverseGalois.CFT.TameFrobenius
import InverseGalois.CFT.TameRamification
import InverseGalois.CFT.Tate.Augmentation
import InverseGalois.CFT.Tate.Averaging
import InverseGalois.CFT.Tate.Basic
import InverseGalois.CFT.Tate.BrauerRelative
import InverseGalois.CFT.Tate.Commensurable
import InverseGalois.CFT.Tate.Congr
import InverseGalois.CFT.Tate.Counting
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
import InverseGalois.CFT.TateCohomology.Abelianization
import InverseGalois.CFT.TateCohomology.Acyclic
import InverseGalois.CFT.TateCohomology.Additive
import InverseGalois.CFT.TateCohomology.Annihilate
import InverseGalois.CFT.TateCohomology.AugmentationIdeal
import InverseGalois.CFT.TateCohomology.CocycleExtension
import InverseGalois.CFT.TateCohomology.CohomTrivial
import InverseGalois.CFT.TateCohomology.Exact
import InverseGalois.CFT.TateCohomology.Functorial
import InverseGalois.CFT.TateCohomology.Graded
import InverseGalois.CFT.TateCohomology.HomologyJunction
import InverseGalois.CFT.TateCohomology.Induced
import InverseGalois.CFT.TateCohomology.Iterate
import InverseGalois.CFT.TateCohomology.Junction
import InverseGalois.CFT.TateCohomology.Norm
import InverseGalois.CFT.TateCohomology.PGroupInvariants
import InverseGalois.CFT.TateCohomology.PGroupTrivial
import InverseGalois.CFT.TateCohomology.PTorsionTrivial
import InverseGalois.CFT.TateCohomology.Restrict
import InverseGalois.CFT.TateCohomology.Shift
import InverseGalois.CFT.TateCohomology.Shifting
import InverseGalois.CFT.TateCohomology.SylowInjective
import InverseGalois.CFT.TateCohomology.RestrictOne
import InverseGalois.CFT.TateCohomology.SylowTrivial
import InverseGalois.CFT.TateCohomology.TateClassCount
import InverseGalois.CFT.TateCohomology.TateDegreeTwo
import InverseGalois.CFT.TateCohomology.TateNakayama
import InverseGalois.CFT.TateCohomology.TateTheorem
import InverseGalois.CFT.TateCohomology.Tensor
import InverseGalois.CFT.TateCohomology.TensorExtension
import InverseGalois.CFT.TateCohomology.TensorFunctor
import InverseGalois.CFT.TateCohomology.TensorPTorsion
import InverseGalois.CFT.TateCohomology.TensorShift
import InverseGalois.CFT.TateCohomology.TensorTrivial
import InverseGalois.CFT.TateCohomology.TorsionFree
import InverseGalois.CFT.TateCohomology.Transfer
import InverseGalois.CFT.TotallyReal
import InverseGalois.CFT.Units.ABHN
import InverseGalois.CFT.Units.ABHNArchimedean
import InverseGalois.CFT.Units.ABHNCoboundary
import InverseGalois.CFT.Units.ABHNFinite
import InverseGalois.CFT.Units.ABHNLocalNorm
import InverseGalois.CFT.Units.ABHNLocalPower
import InverseGalois.CFT.Units.ABHNPlaces
import InverseGalois.CFT.Units.ABHNRamified
import InverseGalois.CFT.Units.ABHNSqrtNegOne
import InverseGalois.CFT.Units.ABHNSqrtNegOneRamified
import InverseGalois.CFT.Units.ABHNTorsion
import InverseGalois.CFT.Units.AdicFixed
import InverseGalois.CFT.Units.AdicIdeleHerbrand
import InverseGalois.CFT.Units.AdicLocalNorm
import InverseGalois.CFT.Units.AdicOrbit
import InverseGalois.CFT.Units.AdicSIdeles
import InverseGalois.CFT.Units.AdicUnitGen
import InverseGalois.CFT.Units.ArchimedeanIdeles
import InverseGalois.CFT.Units.BaseArtin
import InverseGalois.CFT.Units.BaseChangeCocycle
import InverseGalois.CFT.Units.BaseChangeIndex
import InverseGalois.CFT.Units.BaseFundamental
import InverseGalois.CFT.Units.BaseTate
import InverseGalois.CFT.Units.ClassSet
import InverseGalois.CFT.Units.CompletionFinite
import InverseGalois.CFT.Units.CompletionGalois
import InverseGalois.CFT.Units.CompletionHilbert90
import InverseGalois.CFT.Units.CompletionUnits
import InverseGalois.CFT.Units.CompositumEmbed
import InverseGalois.CFT.Units.CompositumFundamental
import InverseGalois.CFT.Units.CyclicTrivial
import InverseGalois.CFT.Units.Decomposition
import InverseGalois.CFT.Units.DecompositionOutside
import InverseGalois.CFT.Units.HasseHom
import InverseGalois.CFT.Units.HasseLevel
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.CFT.Units.HasseInflation
import InverseGalois.CFT.Units.HasseDecomposition
import InverseGalois.CFT.Units.HasseTwo
import InverseGalois.CFT.Units.HasseTwoDecomposition
import InverseGalois.CFT.Units.EquivariantLabel
import InverseGalois.CFT.Units.FirstInequality
import InverseGalois.CFT.Units.FrobeniusPlace
import InverseGalois.CFT.Units.GaloisAction
import InverseGalois.CFT.Units.GeneratingPrimes
import InverseGalois.CFT.Units.GlobalFundamental
import InverseGalois.CFT.Units.GlobalTate
import InverseGalois.CFT.Units.HasseNorm
import InverseGalois.CFT.Units.Herbrand
import InverseGalois.CFT.Units.Idele
import InverseGalois.CFT.Units.IdeleClass
import InverseGalois.CFT.Units.IdeleClassComap
import InverseGalois.CFT.Units.IdeleClassFixed
import InverseGalois.CFT.Units.IdeleClassH1
import InverseGalois.CFT.Units.IdeleClassH1Full
import InverseGalois.CFT.Units.IdeleClassH2
import InverseGalois.CFT.Units.IdeleClassH2Full
import InverseGalois.CFT.Units.IdeleClassH2Tower
import InverseGalois.CFT.Units.IdeleClassIndex
import InverseGalois.CFT.Units.IdeleClassSES
import InverseGalois.CFT.Units.IdeleClassTate
import InverseGalois.CFT.Units.IdeleClassTower
import InverseGalois.CFT.Units.IdeleCoboundary
import InverseGalois.CFT.Units.IdeleFixed
import InverseGalois.CFT.Units.IdeleGen
import InverseGalois.CFT.Units.IdeleNorm
import InverseGalois.CFT.Units.IdeleNormTower
import InverseGalois.CFT.Units.IdeleQuotCyclic
import InverseGalois.CFT.Units.IdeleRep
import InverseGalois.CFT.Units.IdeleRestrict
import InverseGalois.CFT.Units.IdeleTower
import InverseGalois.CFT.Units.InfiniteComap
import InverseGalois.CFT.Units.InfiniteFixed
import InverseGalois.CFT.Units.InfiniteGalois
import InverseGalois.CFT.Units.InfiniteHilbert90
import InverseGalois.CFT.Units.InfiniteIdele
import InverseGalois.CFT.Units.InfiniteOrbit
import InverseGalois.CFT.Units.InfiniteTowerDescent
import InverseGalois.CFT.Units.InflationDescent
import InverseGalois.CFT.Units.LocalCoboundaryTwist
import InverseGalois.CFT.Units.LocalEmbedding
import InverseGalois.CFT.Units.LocalIdele
import InverseGalois.CFT.Units.LocalNorm
import InverseGalois.CFT.Units.LocalPowIdele
import InverseGalois.CFT.Units.LocalSqrtNegOne
import InverseGalois.CFT.Units.NormIndex
import InverseGalois.CFT.Units.OrbitPlaces
import InverseGalois.CFT.Units.PlaceComap
import InverseGalois.CFT.Units.PlaceIdele
import InverseGalois.CFT.Units.PlaceRestrict
import InverseGalois.CFT.Units.PlaceTower
import InverseGalois.CFT.Units.Places
import InverseGalois.CFT.Units.PowIdele
import InverseGalois.CFT.Units.PowSIdeleClass
import InverseGalois.CFT.Units.PowSIdeleNorm
import InverseGalois.CFT.Units.PrimeAbove
import InverseGalois.CFT.Units.RatFundamentalClass
import InverseGalois.CFT.Units.RatSumSquares
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
import InverseGalois.CFT.Units.TowerCoboundary
import InverseGalois.CFT.Units.TowerDescent
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
* `InverseGalois.CFT.FrobeniusStabilizer` generates the decomposition group at a ramified prime by
  the inertia group together with an arithmetic Frobenius, so that the image of the decomposition
  group under a homomorphism lies in the image of the inertia group as soon as the image of the
  Frobenius does.
* `InverseGalois.CFT.Disjoint` shows that number fields with disjoint ramification meet in `ℚ`.
* `InverseGalois.CFT.InertiaSubgroup` identifies the inertia subgroup of a prime with the subgroup
  fixing the prime pointwise once the residue degree is one, and with the whole decomposition group
  once the ramification index is the degree, and follows inertia along the Galois action.
* `InverseGalois.CFT.Compositum` computes the Galois group of a compositum of two Galois
  extensions meeting in the base as the product of their Galois groups.
* `InverseGalois.CFT.CompositumBase` views the compositum as an extension of one of its two
  factors, and identifies its Galois group over that factor with the Galois group of the other
  factor over the base, when the two meet in the base field.
* `InverseGalois.CFT.CentralCompositum` observes that an automorphism of a compositum which is
  trivial on one factor is central as soon as the other factor is abelian over the base, so that
  the subgroup it generates is normal and an involution of the abelian factor is realized as an
  arithmetic Frobenius at infinitely many primes.
* `InverseGalois.CFT.CompositumLift` extends an automorphism of one factor of a compositum which
  fixes the intersection of the two factors to the whole compositum by the identity on the other
  factor, the Galois correspondence turning the intersection of two intermediate fields into the
  join of their fixing subgroups; over the rationals an involution so extended is an arithmetic
  Frobenius at infinitely many primes.
* `InverseGalois.CFT.PiDual` records that a linear form on a finite product of copies of a field is
  the pairing with a vector of coefficients, so that a vector lies in a subspace as soon as it is
  killed by every coefficient vector killing the subspace.
* `InverseGalois.CFT.CharacterSpan` decomposes a character to the group of order two which vanishes
  wherever a jointly surjective finite family of such characters vanishes: it is the sum of a
  subfamily, the character factoring through the joint map as a linear form.
* `InverseGalois.CFT.PrimeProductSquare` identifies a finite set of primes from the product of its
  members: the product of two such products is a square exactly when the two sets coincide, and a
  rational number whose square is a natural number is itself one.
* `InverseGalois.CFT.Multiquadratic` prescribes the signs by which an automorphism moves a finite
  family of square roots: a sign pattern is realized by an automorphism fixing a given intermediate
  field pointwise exactly when it is annihilated by the subsets whose product of square roots
  already lies in that field, the linear functionals on a space of `ZMod 2`-valued functions being
  the subset sums.
* `InverseGalois.CFT.PGroupCompositum` bounds the Galois group of a compositum by the product of
  the Galois groups of its factors, so that a compositum of finitely many extensions of `ℓ`-power
  degree again has `ℓ`-power degree.
* `InverseGalois.CFT.UnramifiedCompositum` computes the ramification of a compositum: a prime
  ramifies in `A ⊔ B` exactly when it ramifies in `A` or in `B`, with no disjointness hypothesis,
  so the level condition passes to a compositum.
* `InverseGalois.CFT.SplitCompositum` does the same for residue degrees, which do not behave so
  simply: the order of a decomposition group is the ramification index times the residue degree,
  and restriction embeds the decomposition group of a compositum into that of one factor as soon
  as the prime splits completely in the other, so residue degree one is inherited.
* `InverseGalois.CFT.SplitSup` draws the conclusion for an arbitrary pair of number fields: a prime
  splitting completely in each of two number fields splits completely in their compositum.
* `InverseGalois.CFT.FrobeniusInvolution` realizes an element of order two generating a normal
  subgroup of the Galois group as the arithmetic Frobenius at a prime avoiding any prescribed
  finite set, by comparing the primes splitting completely in the fixed field of the subgroup it
  generates with those splitting completely in the whole field.
* `InverseGalois.CFT.RelativeFrobenius` runs the same comparison over an arbitrary number field:
  the decomposition group of a prime over the base is the ramification index times the residue
  degree, at an unramified prime it is generated by the arithmetic Frobenius, and an element of
  prime order generating a normal subgroup is the decomposition group at infinitely many primes of
  the base, so the Frobenius there generates the group that element generates.

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
* `InverseGalois.CFT.InertiaFixedField` reads off the ramified primes of the fixed field of a
  subgroup of the Galois group: they are the primes some of whose inertia subgroups escape the
  subgroup.
* `InverseGalois.CFT.SplitInertiaPrime` transports the absorption of a decomposition group by an
  inertia subgroup together with a normal subgroup from one prime above a rational prime to all of
  them, so that split inertia in the fixed field only has to be checked at one prime above each
  ramified rational prime.
* `InverseGalois.CFT.InertiaSurjective` shows that restriction to a normal subextension maps an
  inertia subgroup onto the inertia subgroup of the prime below it, by comparing the orders of the
  two through the multiplicativity of the ramification index in a tower.
* `InverseGalois.CFT.InertiaTransport` records that total ramification at a prime is an
  isomorphism invariant of a number field, so that a field built inside one algebraic closure can
  be moved into another without losing its ramification.
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
* `InverseGalois.CFT.Cyclotomic.TotallyRamified` cuts out of the cyclotomic field of prime-power
  conductor `p ^ k` the cyclic extension of `ℚ` of a prescribed degree dividing `φ (p ^ k)`,
  unramified away from `p` and totally ramified at `p`, which is the character used to correct the
  ramification of a solution of an embedding problem at one prime.
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
* `InverseGalois.CFT.Cyclotomic.EighthRootSubfield` places the eighth cyclotomic layer inside the
  algebraic closure of the rationals and records that it has degree four and that any field
  containing it contains a square root of `-1` and a square root of `2`.

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
* `InverseGalois.CFT.Scholz.BaseChange` adjoins the `ℓ`-th roots of unity to a field of `ℓ`-power
  degree, which the local criterion for the central embedding step needs in its base field, and
  shows that the Galois group is unchanged because the two degrees are coprime.
* `InverseGalois.CFT.Scholz.LocalTransport` reads the local hypotheses of the central embedding
  criterion over the enlarged base field off the arithmetic of the original field, using that
  restriction to that field is injective on the Galois group over the enlarged base.
* `InverseGalois.CFT.Scholz.CompositumTransport` specialises that reading to the compositum of the
  original field with the cyclotomic field, where both factors reappear as copies of themselves.
* `InverseGalois.CFT.Scholz.ProperSolution` solves a central Frattini embedding problem with kernel
  of odd prime order over that compositum, which is where the roots of unity the criterion needs are
  available.
* `InverseGalois.CFT.RestrictLE` restricts an automorphism of an intermediate field to a smaller
  intermediate field that is normal over the base.
* `InverseGalois.CFT.KerField` cuts an intermediate field down to the fixed field of the kernel of a
  homomorphism out of its Galois group, read inside the ambient field, and identifies the Galois
  group of the result with the target of the homomorphism.
* `InverseGalois.CFT.FibreCompositum` presents a group as the fibre product of two of its quotients
  over a common further quotient, whenever the two kernels intersect trivially and together exhaust
  the kernel of the map to it, and transfers that presentation to Galois groups: the compositum of
  two solutions of one embedding problem realizes the fibre product of the two solving groups,
  because a subgroup of the fibre product surjecting onto one factor is everything as soon as the
  kernel of that factor consists of non-generating elements.
* `InverseGalois.CFT.Scholz.BaseDescent` descends a solved central Frattini embedding problem from
  an enlarged base field of degree prime to the order of the kernel back to the original base.
* `InverseGalois.CFT.Scholz.CentralStep` combines the two: the solution obtained over the cyclotomic
  compositum is carried to the normal closure over the rationals and descended there.
* `InverseGalois.CFT.Scholz.ProperSolutionTwo` solves a central Frattini embedding problem with
  kernel of order two directly over the given field, because `-1` is a primitive square root of
  unity in the rationals and the criterion needs no condition at the archimedean place.
* `InverseGalois.CFT.Scholz.CentralStepTwo` records that for a kernel of order two the solution is
  therefore already defined over the rationals, so no base change and no descent are involved.
* `InverseGalois.CFT.CutField` cuts a Galois extension down to the fixed field of the kernel of a
  homomorphism of its Galois group, read inside the ambient field, and identifies the Galois group
  of the result with the target of the homomorphism.
* `InverseGalois.CFT.Scholz.PGroupSolution` applies that cut to the solution produced by the central
  step, so that the solution field has Galois group exactly the group being realised, hence of
  `ℓ`-power degree.
* `InverseGalois.CFT.Scholz.Tame` shows that every field satisfying the level condition with
  `ℓ`-power degree is tamely ramified, so that the tame Kronecker–Weber theorem applies to all of
  them.
* `InverseGalois.CFT.Scholz.BadPrimes` confines the ramification of a Galois number field whose
  inertia subgroups are central and killed by `ℓ` to the prime `ℓ` and the primes congruent to one
  modulo `ℓ`, which is where the correcting cyclotomic characters live.
* `InverseGalois.CFT.Scholz.PGroupInertia` reads the same confinement off a solution of the
  embedding problem rather than off the field: inertia away from `ℓ` in an extension of
  `ℓ`-power degree is cyclic, and a solution whose values on it lie in the kernel kills it unless
  the prime is `ℓ` or congruent to one modulo `ℓ`.
* `InverseGalois.CFT.Scholz.Twist` corrects a solution of a central Frattini embedding problem by a
  character of an auxiliary Galois extension with values in the kernel, over a Galois extension
  containing both fields.
* `InverseGalois.CFT.Scholz.InertiaTwist` records the effect of such a correction on the
  ramification, one prime at a time: at a prime with cyclic inertia a suitable power of the
  character cancels the solution there, and at a prime where both are already unramified nothing is
  lost.
* `InverseGalois.CFT.Scholz.CorrectingCharacter` produces the character used for that correction:
  for a prime equal to the residue characteristic or congruent to one modulo it, a cyclic extension
  of the rationals of degree the residue characteristic, ramified only at that prime and totally
  ramified there, together with the induced character with values in the kernel.
* `InverseGalois.CFT.Scholz.TwistStep` assembles the correction at one prime: the twisted solution
  solves the same embedding problem and its field loses that prime from its ramified set without
  gaining any other.
* `InverseGalois.CFT.Scholz.RamificationControl` iterates that correction over the finitely many
  unwanted primes, so that a solution of a central Frattini embedding problem can be taken to
  ramify only inside a prescribed set of primes; the characters are supplied by normal
  subextensions ramified at one prime each.
* `InverseGalois.CFT.Scholz.InertiaRankOne` isolates the one local fact the correction needs at a
  prime, namely that the solution is already a power of the character on the inertia subgroup
  there; away from the residue characteristic it follows from cyclicity of inertia.
* `InverseGalois.CFT.Scholz.AbelianInertia` reads that local fact inside the decomposition group:
  the values of such a solution on inertia are central, so the solution factors through the
  abelianized decomposition group, where cyclicity of the image of inertia is all that is needed.
* `InverseGalois.CFT.Scholz.CentralCyclicLift` compares such a solution on a decomposition group
  with a homomorphism trivial on inertia: once the residue extension is large enough to admit one,
  the restriction of the solution to inertia extends to a character of the whole decomposition
  group with values in the kernel of the embedding problem.
* `InverseGalois.CFT.Scholz.DecompositionLift` performs that extension at a prime of a number
  field.  The quotient of the decomposition group by the inertia subgroup is the Galois group of
  the residue extension and is cyclic, so a solution which is unramified at the prime, and hence
  takes values in the kernel on inertia, extends over that quotient as soon as the residue degree
  is divisible by the order of the group of the embedding problem.
* `InverseGalois.CFT.Scholz.DyadicResidueDegree` makes the residue degree at two divisible by a
  prescribed power of two.  The residue degree of a prime in a cyclotomic field is the order of
  that prime modulo the conductor, and modulo a Fermat number the class of two has order exactly
  the corresponding power of two, so adjoining a root of unity of Fermat conductor forces the
  residue degree at two upwards while leaving two unramified.
* `InverseGalois.CFT.Scholz.DyadicCorrector` assembles the correcting character at the prime two
  itself, for an embedding problem whose kernel has order two.  The solution extends over the
  decomposition group; over the fixed field of that group the extension, having only two values, is
  cut out by a square root, and the place below is unramified of residue degree one, so in the
  presence of the eighth roots of unity the square root agrees on inertia with a square root of one
  of `1, -1, 2, -2`.  The quadratic character of that rational square root is ramified only at two
  and cancels the solution there.
* `InverseGalois.CFT.Scholz.CorrectingSubfield` carries a correcting character built inside an
  algebraic closure into any larger field containing the subfield it was built on.
* `InverseGalois.CFT.Scholz.UnramifiedSolution` assembles the whole correction: adjoining the
  cyclic extensions attached to the finitely many unwanted primes keeps the degree a power of the
  residue characteristic, and the twisted solution cut down to its own field ramifies nowhere
  outside the field the embedding problem was posed over.
* `InverseGalois.CFT.Scholz.UnramifiedFactorInertia` compares the inertia subgroups of a field
  generated by two normal subextensions with those of one of them: at a prime unramified in the
  other, restriction is injective on inertia, so inertia inherits whatever the Galois group of the
  first subextension satisfies, and in particular is cyclic when that group is a `p`-group and the
  prime is different from `p`.
* `InverseGalois.CFT.Scholz.UnramifiedSolutionTwo` performs the same correction at the residue
  characteristic two.  There the field also carries the eighth cyclotomic layer, which costs
  nothing in the degree and supplies the two square roots the dyadic twist needs, and a cyclotomic
  layer of Fermat conductor, which forces the residue degree at two upwards; the conductor is
  chosen prime to all the unwanted primes, so the inertia subgroups there still sit inside a
  two-group and remain cyclic.
* `InverseGalois.CFT.Scholz.ElementaryAbelianSolutionTwo` extends that solution to an elementary
  abelian kernel.  A character of the kernel splits off a line: the quotient of the problem by the
  kernel of the character has kernel of order two, the quotient by the line has a smaller kernel
  and is solved by induction, and the compositum of the two solutions over the same field realizes
  the fibre product of the two solving groups, which is the whole group and again ramifies nowhere
  outside the field the problem was posed over.
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
* `InverseGalois.CFT.Cyclotomic.QuadraticSubfield` identifies the subfield of degree two, for a
  prime conductor congruent to `1` modulo `4`, with the field generated by a square root of the
  conductor produced by the quadratic Gauss sum, so that its splitting law becomes the statement
  that the primes splitting completely in it are the quadratic residues; quadratic reciprocity
  turns that criterion into a condition modulo the splitting prime instead.
* `InverseGalois.CFT.Scholz.SplitStep` performs one split step concretely, producing the field, its
  Galois group as a product, its degree and its ramified primes.
* `InverseGalois.CFT.Scholz.StepRamification` pins the ramified primes of that step down to an
  equality: ramification propagates upward from both factors, and the new factor is ramified at its
  branching prime because a number field unramified everywhere is the rationals.
* `InverseGalois.CFT.Scholz.StepSqrt` supplies the square root the step carries at the prime two:
  from level two on the branching prime is congruent to one modulo four, so a Gauss sum in the
  cyclotomic field of that conductor squares to it and generates the quadratic new factor, the
  Galois group of a cyclotomic field of prime conductor having a single subgroup of index two.
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
* `InverseGalois.CFT.Scholz.RadicalSplitting` supplies the power residue criterion for such a field:
  a prime congruent to one modulo `ℓ` modulo which the radicand is an `ℓ`-th power splits completely
  in the radical field of that radicand, because an automorphism moving a generator by a root of
  unity congruent to one modulo a prime above it is the identity.
* `InverseGalois.CFT.Scholz.PrimeIndependence` shows that a product of powers of distinct primes is
  an `ℓ`-th power in the rationals only when every exponent is divisible by `ℓ`, the `p`-adic
  valuation reading off the exponents; this is what makes an auxiliary radical genuinely new.
* `InverseGalois.CFT.Scholz.PowerResidue` turns the multiplicative question of being an `ℓ`-th power
  residue into an `𝔽_ℓ`-linear one, the units modulo a prime congruent to one modulo `ℓ` surjecting
  onto a cyclic group of order `ℓ` with the power residues as kernel.
* `InverseGalois.CFT.Scholz.AuxPrimeChoice` chooses the auxiliary primes: a rational number which is
  not an `ℓ`-th power admits infinitely many primes splitting completely in a nilpotent extension
  containing the `ℓ`-th roots of unity but not in the radical field of that number, and such a prime
  fails the power residue criterion for it.
* `InverseGalois.CFT.Scholz.ResidueSymbol` packages the power residue character as a symbol on
  natural numbers, additive on products of units and compatible with pulling a character back along
  the reduction map of a divisor and with multiplying characters.
* `InverseGalois.CFT.Scholz.ResidueSpan` makes the choice of auxiliary primes a piece of linear
  algebra: their symbol vectors span the whole space of `𝔽_ℓ`-valued functions on a finite set of
  primes, so every prescribed vector of symbols is realised by a single character of the units
  modulo a product of auxiliary primes.
* `InverseGalois.CFT.NilpotentCompositum` supplies the group-theoretic ingredient the constraint
  field needs: the compositum of two normal subextensions with nilpotent Galois groups again has a
  nilpotent Galois group, restriction embedding it into the product of the two.
* `InverseGalois.CFT.Scholz.AuxPrimeField` names the constraint field the auxiliary primes are
  required to split completely in — the field being corrected enlarged by the roots of unity of
  order `ℓ ^ k` — and reads off the resulting shape of the modulus: its prime factors avoid the
  prescribed set and `ℓ`, are congruent to one modulo `ℓ ^ k`, and split completely in the field
  being corrected.
* `InverseGalois.CFT.Scholz.FrobeniusDefect` measures what the correction has to cancel: at a prime
  ramified in a subextension with split inertia, the image of an arithmetic Frobenius lies in the
  image of the inertia group up to one element of the kernel, the same element for every arithmetic
  Frobenius at the prime.
* `InverseGalois.CFT.Scholz.FrobeniusSymbol` supplies the character that cancels it: a character of
  the units modulo the modulus, read through the cyclotomic subfield, takes the value recorded by
  the power residue symbol on an arithmetic Frobenius at a prime not dividing the modulus, and
  kills the inertia group there.
* `InverseGalois.CFT.Scholz.PrimeOrderInertia` disposes of the auxiliary primes themselves: where
  the image of a decomposition group lies in a subgroup of prime order, ramification alone forces
  the image of the inertia group to be the whole of it, so the split inertia condition holds for
  free.
* `InverseGalois.CFT.Scholz.ResidueCorrection` puts the correction together: the solution ramifying
  no more than the field below is enlarged by the roots of unity of the auxiliary modulus and
  twisted by the character whose power residue symbols are the Frobenius defects, and the field cut
  out by the twisted solution realises the group of the central step at the required level.
* `InverseGalois.CFT.PairwiseResidue` makes a chain of primes mutually quadratic: a prime congruent
  to one modulo an earlier prime is trivially a square there, and when the earlier prime is
  congruent to one modulo four the law of quadratic reciprocity attaches the same symbol to both
  primes and so turns the residue relation around.
* `InverseGalois.CFT.SqrtCompositumDisjoint` keeps a square root out of a compositum with a field
  ramified elsewhere: the squarefree part of the half coming from the second factor is congruent to
  one modulo four and shares no prime with the radicand or with the other half, so it divides a
  perfect square exactly once unless it is one.
* `InverseGalois.CFT.SqrtFrattini` descends a square root of a base element along a Frattini
  subextension: an automorphism moves such a square root at most to its negative, so the
  automorphisms fixing it are everything or a maximal subgroup, and either way they contain the
  Frattini subgroup.
* `InverseGalois.CFT.SqrtSign` records the sign by which an automorphism moves a square root of a
  base element as a canonical character of the Galois group, additive both in the automorphism and
  in the square root, so that two square roots with the same character have a product of radicands
  which is a square in the base field.
* `InverseGalois.CFT.Scholz.DyadicRadical` clears the cyclotomic layer of the constraint field at
  the prime two: that layer is ramified only at two, so a field unramified at two meets it in the
  rationals and acquires no new square root of an integer congruent to one modulo four.
* `InverseGalois.CFT.Scholz.DyadicSocle` records which exponent vectors the correction at the prime
  two has to avoid — those whose radicand is already a square in the field being corrected — and
  reduces orthogonality to them to summing to zero over each block of a family of ramified primes
  accounting for those square roots.
* `InverseGalois.CFT.Scholz.BlockRealization` supplies such a family: a pairwise disjoint family of
  blocks of primes whose products have square roots in the field with jointly surjective sign
  characters, trivial only on the Frattini subgroup, accounts for every square root of a squarefree
  product of primes there.
* `InverseGalois.CFT.Scholz.BlockGenerators` makes that family easy to carry along an induction:
  when the square roots of the blocks are moved in sign by the distinguished generators of a free
  object of positive `2`-class exactly diagonally, the joint sign character is the coordinate
  character read through the realization, so both conditions hold at once.
* `InverseGalois.CFT.Scholz.MultiquadraticBase` starts the dyadic induction: iterating the split
  step at the prime two from the rationals produces a field satisfying `(S_N)` ramified at exactly
  as many distinct primes as the number of quadratic layers, with elementary abelian Galois group —
  the free object of that rank and `2`-class one — and with each ramified prime a block of its own,
  equipped with a square root.
* `InverseGalois.CFT.Scholz.MultiquadraticSqrt` matches those square roots to the generators: a
  product of a nonempty subfamily of them is irrational, so every sign pattern is realized by an
  automorphism and the joint sign character, the two groups having the same order, is an
  isomorphism onto the free object of rank `d` and `2`-class one.
* `InverseGalois.CFT.Scholz.StrongScholz` carries that data as the invariant of the induction on
  the `2`-class: a Scholz field realising a free object together with a pairwise disjoint family of
  blocks accounting for its square roots; the multiquadratic base supplies the case of class one,
  and a strong Scholz realization of every free object realises every finite `2`-group.
* `InverseGalois.CFT.Scholz.DyadicClassStep` solves the rung of the tower of free objects with no
  new ramification at all, the blocks of the realization below carrying over to the solution because
  the rung is a Frattini extension.
* `InverseGalois.CFT.Scholz.SubfieldScholz` reads Serre's condition on a subfield: a prime ramified
  in a field of split inertia has residue degree one in every subfield, so it splits completely in
  every subfield it does not ramify in.
* `InverseGalois.CFT.Scholz.DyadicShrink` shrinks a strong Scholz realization along a vector of
  bits: collapsing the free object of rank `d * r` onto the one of rank `d` cuts out a subfield
  whose blocks are the unions of the blocks the vector selects.
* `InverseGalois.CFT.Scholz.ClassStepData` carries a rung of the induction — a realization together
  with a field above it realising the next class and ramifying harmlessly over it — and shrinks the
  realization and the field above it at the same time.
* `InverseGalois.CFT.Scholz.DyadicStepUp` reads a Scholz solution of the rung over a strong Scholz
  realization as a strong Scholz realization of the next class, with the very same blocks.
* `InverseGalois.CFT.Scholz.DyadicInduction` isolates the step that raises the `2`-class by one and
  runs the induction from it: granted that step, every finite `2`-group is a Galois group over `ℚ`.
* `InverseGalois.CFT.Scholz.DyadicResidueCorrection` is the correction itself at the prime two: a
  solution whose Frobenius defects sum to zero over each such block realises the group of the
  central step at the required level.
* `InverseGalois.CFT.Scholz.SplitInertiaAt` reads Serre's residue-degree condition one prime at a
  time and identifies it with the statement that an arithmetic Frobenius above the prime lies in the
  inertia group, hence with the vanishing of the defect a solution of a central step carries there.
* `InverseGalois.CFT.Scholz.CanonicalDefect` turns that identification into the Scholz obstruction of
  a prime: a solution preferring the trivial defect carries the defect zero exactly at the primes of
  split inertia, so the orthogonality the correction asks for depends on nothing but the field below
  and the family of blocks.
* `InverseGalois.CFT.Scholz.BlockDefect` sums that obstruction over a block and reads the
  orthogonality condition of the correction as the obstruction of the block; over a fixed cover the
  obstruction of a prime in the subfield cut out by a normal subgroup is a membership statement in
  the group, an arithmetic Frobenius lying in the inertia subgroup together with that subgroup.
* `InverseGalois.CFT.Scholz.CoverInertia` computes the central part of that inertia subgroup: over a
  cover realising a free object of one class higher, the inertia at a prime of the block of an index
  meets the kernel of the projection in the cyclic group generated by the coordinate generator of
  that index.
* `InverseGalois.CFT.Scholz.CentralDefect` factors an arithmetic Frobenius into an inertia part and a
  central part and reads the obstruction of the prime in every subfield cut out by a subgroup of the
  central subgroup off the central part alone.
* `InverseGalois.CFT.Scholz.DyadicLiftCorrection` makes the correction on a cover available at the
  prime two from that reading: it is enough that the obstructions of the field cut out by the
  uncorrected solution sum to zero over each block.
* `InverseGalois.CFT.Scholz.DyadicStageTransition` compares two of those readings: adjoining to a
  subgroup the element a stage of the dyadic climb is built on leaves the obstruction of every block
  unchanged, so the climb carries its hypothesis from one stage to the next.
* `InverseGalois.CFT.Scholz.DyadicStage` is the climb itself: a stage is a cover together with the
  subgroup of the kernel it has cut down to, and cutting that subgroup along a family of characters
  separating its points ends at the trivial subgroup, where the cover is a strong Scholz realization
  of the free object of the next `2`-class.
* `InverseGalois.CFT.Scholz.CoverObstruction` reads the obstruction of a prime of a block in every
  subfield cut out of a solution at once, off a generator of the inertia subgroup at the prime and
  the central part of an arithmetic Frobenius above it.
* `InverseGalois.CFT.Scholz.DyadicInitialStage` starts the climb by paying with rank: over a
  realization of the free object of `r` times the rank, the vector of bits a counting argument
  supplies collapses the copies of every row to a block whose obstruction vanishes against every
  hyperplane, which raises the `2`-class of the induction by one.
* `InverseGalois.CFT.Scholz.SplitInertiaTower` carries that obstruction along a tower: it vanishes in
  every subfield of a field where it vanishes, it vanishes upstairs whenever the prime is totally
  ramified in the top layer, and in a compositum whose inertia over the base already lies in one
  factor it is read off the other factor alone.
* `InverseGalois.CFT.Scholz.FrattiniSolution` collects the three stages into the central step of the
  induction itself: at an odd prime, the rank one condition on the inertia subgroup at the residue
  characteristic is the only hypothesis the central embedding step still rests on.
* `InverseGalois.CFT.Scholz.FixedFieldRamification` reads the local behaviour of an intermediate
  field off the position of its subgroup relative to the decomposition group: the ramification index
  times the residue degree of the prime below the fixed field of a subgroup is the index of the
  intersection of the decomposition group with that subgroup.
* `InverseGalois.CFT.Scholz.AbelianInertiaTransport` moves the image of inertia in the abelianized
  decomposition group along any homomorphism of Galois groups carrying decomposition into
  decomposition and inertia onto inertia, which covers both restriction to a normal subextension and
  an isomorphism of number fields.
* `InverseGalois.CFT.Scholz.FrattiniInertia` deduces cyclicity of the abelianized inertia subgroup
  from smallness of its image in the Frattini quotient: if that image has order at most `ℓ` and the
  cyclic quotient of the decomposition group by inertia is large, every element of the
  decomposition group is a power of one fixed element times an element of inertia.  The largeness is
  arranged by adjoining a cyclic extension in which `ℓ` is inert, and cyclicity descends again.
* `InverseGalois.CFT.Scholz.FrattiniInertiaSmall` proves that smallness for a field containing a
  primitive `ℓ`-th root of unity.  The fixed field of the intersection of the decomposition group
  with the kernel of the cyclotomic character has ramification index times residue degree at most
  `ℓ - 1` below the prime, so the local data at a cyclotomic place is available there, and the
  resulting character dichotomy transports along a homomorphism whose image of inertia is an
  `ℓ`-group.
* `InverseGalois.CFT.Scholz.FrattiniInertiaBound` removes the root of unity by passing to the
  compositum with the cyclotomic field, which is no longer an `ℓ`-extension but still has an
  `ℓ`-group as the image of inertia.  The rank one condition is therefore a theorem at every odd
  prime, and with it the central embedding step of the induction.

## Group extensions and the Brauer group

* `InverseGalois.CFT.GroupCohomology.OfCocycle` turns a multiplicative `2`-cocycle into a group
  extension, and `InverseGalois.CFT.GroupCohomology.ToCocycle` turns a group extension into its
  cohomology class, splitting exactly when the class vanishes.
* `InverseGalois.CFT.GroupCohomology.Classification` closes the circle: the second cohomology
  group of `G` with coefficients in `M` is in bijection with the extensions of `G` by `M`, and
  vanishes exactly when every such extension splits.
* `InverseGalois.CFT.GroupCohomology.ExtensionMap` compares two extensions joined by a morphism:
  the factor set of the upper one, pushed forward along the map of kernels, is the factor set of
  the lower one pulled back along the map of quotients, up to the coboundary of the function
  comparing the two sections.
* `InverseGalois.CFT.GroupCohomology.Pullback` reads an embedding problem as a single extension:
  the fibre product of the middle term of an extension with a group mapping into the quotient is an
  extension of that group by the same kernel, its factor set is the original factor set read through
  that map, and it splits exactly when the map lifts.  For an abelian kernel the embedding problem
  is therefore solvable exactly when the pulled back cohomology class vanishes.
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
* `InverseGalois.CFT.Brauer.RelativeIndex` cuts a relative Brauer group along a tower
  `K ⊆ L ⊆ M`: restriction `Br(M / K) → Br(M / L)` has kernel `Br(L / K)`, so the order of
  `Br(M / K)` is at most the product of the orders of the two steps.
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
* `InverseGalois.CFT.Brauer.BaseChangeCentralizer` computes the effect of extending scalars to a
  subfield `L` of a central simple algebra `A`: the algebra `L ⊗[K] A` is the algebra of
  `[L : K]` by `[L : K]` matrices over the centralizer of `L` in `A`.
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
* `InverseGalois.CFT.Brauer.CrossedProductRestrict` restricts a crossed product to an intermediate
  field `M`: the automorphisms fixing `M` span the centralizer of the copy of `M`, so extending
  scalars to `M` sends the Brauer class of a cocycle to the class of its restriction to
  `Gal(L/M)`.
* `InverseGalois.CFT.Brauer.CrossedProductCompositum` extends a crossed product along a field that
  need not be intermediate: an isomorphism between the Galois group of a second extension and the
  Galois group of the first, compatible with the embedding of the first top field, transports the
  cocycle, and extension of scalars sends the Brauer class of the cocycle to the class of its
  transport.
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
* `InverseGalois.CFT.Brauer.CyclicTower` compares the cyclic algebras of the two steps of a tower
  `K ⊆ L ⊆ L'` of cyclic extensions: a simple algebra of the right dimension containing a copy of
  `L` and a unit conjugating it by a generator is the corresponding cyclic algebra, matrices over
  such an algebra are the cyclic algebra of `L'`, and consequently the class of `(L / K, σ, a)` is
  the class of `(L' / K, σ', a ^ [L' : L])` when `σ` is the restriction of `σ'`.
* `InverseGalois.CFT.Brauer.SolvableBound` propagates a bound `|Br(E / F)| ≤ [E : F]` from cyclic
  extensions to solvable ones, by a dévissage that splits off the cyclic subgroup generated by one
  automorphism in the abelian case and the last nontrivial derived subgroup in the solvable case.
  The class carrying the cyclic bound is a class of extensions rather than of fields, and is asked
  to be inherited by both halves of the tower that a group of automorphisms cuts out, which is
  exactly what each step of the dévissage produces.
* `InverseGalois.CFT.Brauer.SolvableNormBound` restates the hypothesis of that dévissage as a
  statement about norms alone: if the norm subgroup of every cyclic extension has index at most the
  degree, then `|Br(L / K)| ≤ [L : K]` for every solvable extension.
* `InverseGalois.CFT.Local.SubfieldValued` restricts a valuation along a map of fields: the
  restricted valuation induces the subspace topology, so a closed subfield of a complete valued
  field is complete, and the residue characteristic and the finiteness of the graded pieces of the
  additive filtration both descend.
* `InverseGalois.CFT.Local.FixedFieldValued` applies this to the subfield fixed by a group of
  automorphisms preserving the valuation.  That subfield is an intersection of equalisers of
  continuous maps, hence closed; the norm of an element of nontrivial value is fixed and has
  nontrivial value, so the restricted value group is still nontrivial; and the isometry hypothesis
  passes to both halves of the tower, downwards by lifting an automorphism to the larger field and
  upwards by restricting scalars.
* `InverseGalois.CFT.Local.CompleteNormIndex` is the local first inequality: for a cyclic extension
  whose larger field is complete and discretely valued, the Herbrand quotient of the unit group is
  the degree and Hilbert's theorem 90 makes its denominator one, so the norm subgroup of the base
  has index exactly the degree.
* `InverseGalois.CFT.Local.CyclicNormIndex` removes the hypotheses on the larger field: a finite
  extension of a complete, discretely valued, locally compact field carries all the structure of a
  local field for the valuation transported by the field norm, whatever the ramification, and the
  automorphisms over the base preserve that valuation because they do not change the norm.  So
  **the norm index of any cyclic extension of a local field is its degree**, and a cyclic extension
  of degree bigger than one always has a unit of the base field which is not a norm.
* `InverseGalois.CFT.Local.KummerNonNorm` reads that off for a radical extension.  Over a local
  field with a primitive `q`-th root of unity, `q` prime, an element which is not a `q`-th power
  generates a cyclic extension of degree `q`, so **some unit of the base field is not a norm from
  it**: the norm residue symbol is nondegenerate in its second argument.
* `InverseGalois.CFT.Brauer.LocalBrauerBound` feeds the two into the dévissage: the extensions
  whose larger field is complete and discretely valued with the automorphisms acting by isometries
  are closed under the dévissage and satisfy the cyclic norm index bound, so the relative Brauer
  group of every solvable extension of local fields has order at most the degree.
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
* `InverseGalois.CFT.GroupCohomology.CyclicTate` matches that description with the zeroth Tate
  group of a single automorphism.  The invariants of a finite cyclic group are the fixed points
  of a generator and the norm of the group action is the norm operator of that generator, so
  **the second cohomology of a finite cyclic group is the zeroth Tate group of the automorphism
  by which a generator acts**; the integral module structure of a representation being unique,
  the comparison of the two descriptions is an isomorphism of representations.
* `InverseGalois.CFT.GroupCohomology.CyclicTateMap` writes that comparison as the class of an
  explicit two-cocycle, whose value at a pair of elements is the point itself exactly when their
  discrete logarithms add up to at least the order of the group.  A homomorphism of finite cyclic
  groups of the same order carrying a generator to a generator preserves discrete logarithms, so
  **the comparison is natural**: the functorial map on second cohomology carries the class of a
  fixed point to the class of its image.
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
* `InverseGalois.CFT.Global.NegOneSymbol` reads the product formula backwards for the pair
  `(-1, d)`: the symbol against `-1` is trivial at every prime congruent to one modulo four, so
  for an integer all of whose odd prime factors are of that shape the dyadic symbol against `-1`
  is exactly the sign, while a prime congruent to three modulo four is positive and has
  nontrivial dyadic symbol.
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
* `InverseGalois.CFT.Global.ReciprocityOmit` drops one *finite* place from that principle instead
  of the real one: with the real symbol given and all but one of the finite symbols trivial, the
  product formula supplies the remaining one, so a rational which is everywhere locally a norm
  except possibly at a single prime is a norm.
* `InverseGalois.CFT.Herbrand` proves the counting theorem behind the Herbrand quotient: for a
  finite commutative group with an automorphism of finite order, the fixed points modulo the norms
  and the norm kernel modulo the differences have the same index.
* `InverseGalois.CFT.Tate.Basic` names those two subquotients the Tate groups of the module, and
  makes them functorial in equivariant homomorphisms.
* `InverseGalois.CFT.Tate.H0Norm` annihilates the upper Tate group by its own order: a fixed point
  multiplied by that order, or by any multiple of it, lies in the image of the norm; when the group
  vanishes altogether every fixed point is itself a norm.
* `InverseGalois.CFT.Tate.Counting` closes a counting argument with those two ingredients: when an
  equivariant homomorphism induces a surjection of zeroth Tate groups, the source is bounded by the
  exponent and the target carries a class of exactly that order, the surjection is forced to be a
  bijection, so **a fixed point whose image has the largest possible order is a norm**.
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
* `InverseGalois.CFT.Kummer.CongruentRadical` sharpens that bound at the exponent itself.  There a
  radical extension is usually ramified, and the criterion which separates the radicands that
  ramify from those that do not is a congruence: if the radicand is a unit at the place and
  congruent to one modulo the `p`-th power of `ζ - 1`, then the radical itself is congruent to one
  modulo `ζ - 1`, because the differences of the radical and the `p`-th roots of unity all have the
  same valuation and their product is the radicand minus one.  So the quotient of the radical minus
  one by `ζ - 1` is integral at the place, and an element of the inertia group moves an integral
  element inside the place; but it multiplies the radical by a `p`-th root of unity, and a
  nontrivial one has the same valuation as `ζ - 1` after subtracting one, so the root of unity is
  trivial and the radical is fixed.
* `InverseGalois.CFT.Kummer.DyadicSquareClass` supplies that congruence at the exponent two, where
  the roots of unity are already rational and `ζ - 1` is `-2`.  At a place where two is a
  uniformizer and the residue field has two elements, multiplying a nonzero element by one or two
  makes the exponent of the uniformizer even, and multiplying the remaining unit by a sign makes it
  congruent to one modulo four: for a unit `u` the two halves `(u + 1) / 2` and `(u - 1) / 2` differ
  by one, so the residue field, having no room for two distinct nonzero residues, puts one of them
  in the place.  So the four rational numbers `1, -1, 2, -2` already meet every square class.
* `InverseGalois.CFT.Kummer.DyadicPlace` reads those two properties off the local invariants.
  Ramification index one says that two lies in the place and not in its square, which is the same as
  saying that its valuation is that of a uniformizer; residue degree one says that the rational
  integers surject onto the residue field, and two lies in the place, so only the residues of zero
  and one remain.  Clearing a denominator which is a unit at the place extends the second statement
  from the algebraic integers to every element integral at the place.
* `InverseGalois.CFT.Kummer.DyadicInertiaChar` turns that square class into an agreement of
  characters.  Multiplying the radicand of a square root by the rational number which puts it in the
  trivial class produces, once the eighth roots of unity are available, a radical of a radicand
  congruent to one, which the inertia group at the place fixes; and the fixed radical is the product
  of the original square root with a square root of one of `1, -1, 2, -2`, so the two are moved
  alike by the inertia group.
* `InverseGalois.CFT.Kummer.QuadraticChar` packages a square root of a rational number as a
  character.  An automorphism moves such a square root to plus or minus itself, and the sign is
  multiplicative, so sending the nontrivial sign to a prescribed element of order dividing two of an
  arbitrary group gives a character with values in that group.  For the radicands `1, -1, 2, -2` the
  radicand is a unit at every place away from two, so the character is trivial on the inertia group
  everywhere except at two.
* `InverseGalois.CFT.Kummer.QuadraticGenerator` produces the square root in the first place.  A
  character of the Galois group of a finite Galois extension whose image has two elements is cut out
  by the difference of an element fixed by its kernel with the image of that element under an
  automorphism outside the kernel: the kernel fixes the difference, the automorphism negates it, so
  its square lies in the base field and the automorphisms fixing it are exactly the kernel.
* `InverseGalois.CFT.Kummer.LevelOne` measures how far a radicand is from that congruence.  The
  *level* of a unit at a place is the power of the uniformizer to which it is congruent to one, and
  the congruence above asks for level at least the exponent.  At a place where the uniformizer is
  `ζ - 1` an automorphism of the base raising `ζ` to the power `g` also raises a radicand to the
  power `g`, up to an exponent-th power, because the extension it generates is abelian; expanding
  both sides of that identity to two terms of their binomial series and comparing the coefficients
  of the uniformizer shows that the level `n` of such a unit satisfies `g ^ n ≡ g` modulo the place.
  Below the exponent that congruence forces level one, so between one and the exponent no level
  occurs at all.
* `InverseGalois.CFT.Kummer.RadicandLevel` collects the data of such a place into a single
  hypothesis and draws the consequence.  The valuation of a radicand is an exponent-th power of the
  valuation of the uniformizer, since the automorphism multiplies it by a power prime to the
  exponent and fixes it; dividing by a power of the uniformizer and by the residue makes it a unit
  congruent to one, the residue being restored by Fermat's little theorem.  The level of that unit
  is one or at least the exponent, and two units of level one agree modulo the square of the
  uniformizer after dividing one by a power of the other, because the residue field of the place
  has exactly as many elements as the exponent.  So of any two radicands either the first is
  congruent to one, or a power of it divides the second into one that is: the radicands form a
  cyclic group modulo the ones satisfying the congruence.
* `InverseGalois.CFT.Kummer.RadicalCharacter` attaches a radical to a character.  A character of
  the Galois group with values in the integers modulo the exponent becomes, after composing with a
  root of unity of the base, a one-cocycle with values in the units of the extension, so Hilbert's
  theorem 90 produces an element which every automorphism multiplies by the corresponding root of
  unity; its power by the exponent is fixed and so lies in the base.  If the extension is abelian
  over a smaller field, an automorphism of the base moves that radicand by the exponent through
  which it acts on the roots of unity, up to a power: the radicand is an eigenvector.
* `InverseGalois.CFT.Kummer.InertiaBound` bounds the inertia group of an abelian extension of
  prime exponent at a place over that prime.  Two independent elements of the inertia group would
  be separated by a pair of characters, whose radicands are eigenvectors; but of two eigen
  radicands one is congruent to one after dividing by a power of the other, and a radicand
  congruent to one modulo the power of the different has a radical fixed by the inertia group.  So
  the inertia group is cyclic of order at most the exponent.
* `InverseGalois.CFT.Kummer.CyclotomicPlace` assembles the abstract local data at a cyclotomic place
  from a number field with a primitive `ℓ`-th root of unity `ζ` and a place above `ℓ` of residue
  degree one at which `ζ - 1` is a uniformizer: the product of the differences `ζ ^ k - 1` gives the
  valuation of `ℓ`, the binomial expansion gives the action on the uniformizer of an automorphism
  raising `ζ` to a primitive root, and the residue field being the prime field makes the identity a
  Frobenius.
* `InverseGalois.CFT.Kummer.RamifiedCyclotomicPlace` recognises such a place by a numerical bound.
  The valuation of a rational prime at a place above it is the exponential of minus the ramification
  index, and `ζ - 1` divides `ℓ` to the depth `ℓ - 1`, so a place whose ramification index times
  residue degree is at most `ℓ - 1` has ramification index exactly `ℓ - 1` and residue degree one.
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
* `InverseGalois.CFT.Units.AdicLocalNorm` settles two cases of that local condition.  At a place
  that splits completely the norm operator of the trivial decomposition group is the identity, so
  every local unit of the base field is a norm.  At a place whose decomposition group is cyclic and
  fixes a uniformizer, the zeroth Tate group of the units of the valuation ring of the completion
  vanishes, and a unit coming from below is fixed there, so it is a norm.
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
* `InverseGalois.CFT.Local.UnitRootPower` sharpens this at a finite place for an exponent prime to
  the residue characteristic, where no accuracy at all is needed beyond a congruence modulo the
  maximal ideal.  The units congruent to one form a pro-`p` group, because raising to the residue
  characteristic moves such a unit one step up the filtration; so a unit congruent to one becomes,
  after enough such raisings, a power with the prescribed exponent, and a Bezout relation between
  the exponent and a power of the residue characteristic turns that into a root of the unit itself.
  The same pro-`p` property shows that a unit congruent to one whose order is prime to the residue
  characteristic is trivial, which makes the roots rigid: over a prime residue field every element
  of the valuation ring is congruent to a rational integer, so a valuation preserving automorphism
  moves a root of unity of order prime to the residue characteristic by a unit congruent to one.
* `InverseGalois.CFT.Local.UnitPowRoot` records where those roots live.  The root produced by the
  exponential is itself the exponential of a small element, so it is again congruent to one, and
  the Bezout relation keeps that property because a step of the filtration is a group.  Together
  with the triviality of a unit congruent to one of order prime to the residue characteristic this
  says that **raising to an exponent prime to the residue characteristic is a bijection of the
  units congruent to one**, which is what lets a root of unity be pinned down inside a prescribed
  class modulo the maximal ideal.
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
* `InverseGalois.CFT.GrunwaldWang` is the Grunwald–Wang theorem, the comparison of the classes of
  the multiplicative group of a number field modulo `n`-th powers with their images in the
  completions.  Prescribing finitely many of the local classes is the weak approximation just
  described.  Conversely an element which is an `n`-th power in almost every completion is an
  `n`-th power, for `n` squarefree: for a prime exponent and a base carrying the roots of unity
  this is Kummer theory read against the previous item, an element which is not a `p`-th power
  generating a cyclic extension of degree `p` by a radical which the decomposition group at a place
  fixes exactly when the radicand is a local `p`-th power there, so that the hypothesis makes almost
  every place split completely and the extension trivial.  The root of unity is removed by adjoining
  it, the cyclotomic extension having degree prime to `p` so that the norm carries a `p`-th root
  down, and a squarefree exponent is assembled from its prime factors by their Bezout relations.
  Wang's counterexample lives at the exponent `8`, which is not squarefree, so no case is lost.
* `InverseGalois.CFT.Units.DecompositionOutside` runs the argument that the decomposition groups
  generate the Galois group against that sharper input.  Throwing away finitely many places of the
  base field, and all the infinite places, costs nothing: the decomposition groups at the finite
  places whose place below avoids a prescribed finite set already generate a solvable Galois group,
  because in the fixed field of the subgroup they generate every place of the base field outside the
  prescribed set splits completely.
* `InverseGalois.CFT.Units.HasseHom` reads that generation statement as one about homomorphisms out
  of the Galois group, where the solvability hypothesis becomes free.  A homomorphism into a
  commutative group has a normal kernel whose fixed field is a quotient of the Galois group
  embedding in that commutative group, hence abelian; so if every automorphism fixing a place lies
  in the kernel then every place splits completely in a solvable subextension, which is therefore
  trivial, and **a homomorphism of the Galois group of an arbitrary Galois extension of number
  fields into a commutative group killing every decomposition group is trivial** — finitely many
  places, and all the infinite places, being discardable as before.
* `InverseGalois.CFT.Units.HasseLevel` carries that statement to an infinite extension, which has no
  places of its own while each of its finite Galois levels is a number field and has them.  An
  automorphism of the big field is local at a place of a level when its restriction to that level
  fixes a place there, and a homomorphism into a commutative group killing a level factors through
  the Galois group of the level, where the automorphisms local at a place of the level are exactly
  the decomposition groups; so **a homomorphism killing a level and every automorphism local at a
  place of that level is trivial**, and for coefficients acted on trivially this is the vanishing of
  the everywhere locally trivial classes of the first cohomology.
* `InverseGalois.CFT.Units.InfiniteDecomposition` supplies the places that an infinite extension
  lacks.  Its ring of integers still has nonzero primes, it is the ring of invariants of the ring of
  integers of the base, the action is continuous for the discrete topology because the stabiliser of
  an integer is open, and the Galois group is profinite; so **the Galois group of an arbitrary
  Galois extension acts transitively on the primes of its integers above a prime of the base**, and
  an automorphism of a level fixing a place there is the restriction of an automorphism fixing a
  prime above.  Hence **a homomorphism killing a level and the stabiliser of every nonzero prime is
  trivial**, and with trivial coefficients **a class dying on every decomposition subgroup
  vanishes** — which is the local condition in the shape a local-global principle states it.
* `InverseGalois.CFT.Units.HasseInflation` spends that on a class of the first cohomology of an
  infinite Galois group whose coefficients are acted on through a finite Galois level.  Restriction
  of scalars identifies the subgroup fixing that level with the Galois group of the big field over
  it, and there the level acts trivially, so a cocycle becomes a homomorphism into the
  coefficients; local triviality makes it kill the decomposition groups of a level above, hence
  vanish, and vanishing on the subgroup fixing a level is exactly the condition for a class to come
  from that level.  So **an everywhere locally trivial class is inflated from the field
  trivialising its coefficients.**
* `InverseGalois.CFT.Units.HasseDecomposition` restates that with the local conditions taken at the
  decomposition subgroups rather than at the places of a level: **a class dying on the stabiliser of
  every nonzero prime of the ring of integers of the top field is inflated from the field
  trivialising its coefficients**, with no level left in the hypothesis.
* `InverseGalois.CFT.Units.HasseTwo` does the same one degree up, with the roots of unity of the
  base field for coefficients.  A class of the second cohomology of the absolute Galois group is
  represented by a two-cocycle inflated from a finite Galois level, and there its values are units
  of the base field, so the Albert-Brauer-Hasse-Noether theorem applies to it: a splitting at every
  place of the level, archimedean places included, makes the level cocycle the coboundary of a
  one-cochain of units of the level, and Kummer theory rescales that cochain over a further radical
  extension until its values are roots of unity again.  Read on the absolute Galois group through
  restriction to the larger level, the rescaled cochain is smooth, so **an everywhere locally
  trivial class of the second cohomology with roots of unity coefficients is trivial** — and
  nothing is assumed about the number of roots of unity, so the prime `2` is covered as well.
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
* `InverseGalois.CFT.Local.RootOfUnityValued` separates the roots of unity of order invertible in
  the residue field.  The nontrivial differences `1 - ζ ^ i` of a primitive `m`-th root of unity
  multiply to `m`, so when `m` has valuation one each of them does too, and **two `m`-th roots of
  unity whose difference has valuation less than one are equal.**  That rigidity is what makes a
  Frobenius canonical: an automorphism raising the valuation ring to the `q`-th power modulo the
  maximal ideal has no choice but to send such a `ζ` to `ζ ^ q`, so an extension generated by one
  of them has at most one Frobenius, whose `j`-th power raises `ζ` to the `q ^ j`-th power.
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
* `InverseGalois.CFT.Local.UnramifiedInvariant` reads that vanishing as a computation of the upper
  Tate group of the multiplicative group of the field: the valuation of a norm is the degree times
  the valuation, so it descends to a map to the integers modulo the degree, the uniformizer in the
  fixed field makes it surjective, and the surjectivity of the norm on the units of the valuation
  ring makes it injective.  This is the invariant map of local class field theory in the unramified
  case.
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
* `InverseGalois.CFT.GroupCohomology.IndexTwo` is the inflation-restriction sequence in degree two
  for a normal subgroup with two cosets, written out on cochains.  Three explicit corrections by
  coboundaries make a two-cocycle whose restriction to the subgroup is a coboundary trivial at
  every pair with an entry in the subgroup, and what is left is the single value at the pair of
  coset representatives, which the cocycle relation forces to be invariant.  That inflated cocycle
  is itself a coboundary exactly when its value is a norm from the invariants of the subgroup, so
  the quotient of the invariants by those norms measures the whole obstruction.
* `InverseGalois.CFT.GroupCohomology.Inflation` is the injectivity of inflation in degree two for an
  arbitrary normal subgroup whose first cohomology vanishes.  A cochain trivialising an inflated
  cocycle need not itself be inflated, but the inflation identity makes its failure to be constant
  on a coset a one-cocycle of the subgroup, and dividing by the coboundary which trivialises that
  one-cocycle leaves the differential unchanged, so **a cochain trivialising an inflated cocycle can
  be chosen constant on cosets and invariant under the subgroup**.
* `InverseGalois.CFT.GroupCohomology.InflationRestriction` is the other half of the sequence in
  degree two, for an arbitrary normal subgroup: a choice of coset representatives replaces the two
  named cosets of the index-two case, and the same three corrections show that **a two-cocycle whose
  restriction to a normal subgroup with vanishing first cohomology is a coboundary is cohomologous
  to an inflated cocycle**.  Combining the two halves gives the dévissage that a group has vanishing
  second cohomology as soon as a normal subgroup and the quotient do.
* `InverseGalois.CFT.GroupCohomology.InfResTwo` reads that analysis back into the language of
  representations over the integers, where a two-cocycle whose restriction to a normal subgroup with
  vanishing first cohomology dies is the inflation of a two-cocycle of the quotient with values in
  the invariants.  The count which that exactness yields is the point: **a group whose kernel under
  one map lies in the image of another has at most as many elements as the product**, so the second
  cohomology of a group is bounded by the second cohomology of the quotient times the second
  cohomology of the subgroup.
* `InverseGalois.CFT.GroupCohomology.InfResTwoInjective` is the other end of the same sequence, in
  the same language: **inflation in degree two is injective** once the first cohomology of the
  subgroup vanishes, because a cochain trivialising an inflated cocycle can be taken constant on
  cosets and fixed by the subgroup, and such a cochain descends to the quotient.  So an inflated
  class has exactly the order of the class it is inflated from, which is how a lower bound for the
  second cohomology of a quotient is carried upwards.
* `InverseGalois.CFT.GroupCohomology.DisjointFundamental` runs both ends of that sequence at once,
  for a finite group generated by two normal subgroups of the same order which meet trivially, one
  of them cyclic.  A class of the largest possible order on the invariants of the first subgroup is
  inflated to the whole group and restricted to the second; naturality of the comparison map of a
  cyclic group identifies the restriction with the class of the same point computed on the second
  subgroup, which vanishes because the counting argument makes the point a norm.  So the class
  descends, and **the second cohomology of the quotient by the second subgroup carries a class
  whose order is divisible by the common order of the two subgroups.**
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
* `InverseGalois.CFT.GroupCohomology.Duality` pairs cochains with chains by evaluating a function on
  a set against a finitely supported family of functionals, one index at a time.  The pairing is
  nondegenerate on both sides, and the differentials of the cochain complex of a representation and
  of the chain complex of its contragredient are adjoint, so cocycles annihilate boundaries and
  cycles annihilate coboundaries.  For a finite group acting on a finite dimensional space the
  induced pairing is perfect: **the first homology of the contragredient representation is
  canonically the dual of the first cohomology**.
* `InverseGalois.CFT.GroupCohomology.TateTwist` multiplies the action of a representation by a
  character of the group.  The linear maps into the one dimensional representation of a character
  are the dual representation twisted by the character, and the dual of a twist is the dual twisted
  by the inverse character, so evaluation onto the double dual identifies **the dual of the linear
  maps into the representation of a character with the twist by the inverse character** — the shape
  in which a Tate twist appears.  Feeding that identification into the duality above, the first
  homology of the twist surjects onto the dual of any subspace of the first cohomology of those
  linear maps.
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
* `InverseGalois.CFT.GroupCohomology.CyclicSubgroup` refines that criterion to a two-cocycle whose
  values lie in a prescribed subgroup: only the elements of that subgroup need be norms, since the
  product of the values of the normalised cocycle along a generator carries the cohomology class and
  again lies in the subgroup.  When the subgroup consists of invariant elements the norm is a power,
  so the criterion becomes the concrete demand that each value be a power of an invariant element
  with exponent the order of the group.
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
* `InverseGalois.CFT.Kummer.CocycleDescent` assembles those three into the field-theoretic half of
  the embedding problem.  A cocycle of `n`-th roots of unity of the base field which is a coboundary
  in the units of a finite Galois extension `K/k` is, after adjoining an `n`-th root of the element
  supplied by Hilbert 90 and taking the Galois closure, **the coboundary of a cochain valued in the
  `n`-th roots of unity of the base field itself**.
* `InverseGalois.CFT.Units.ABHNCoboundary` rewrites the Albert-Brauer-Hasse-Noether theorem
  multiplicatively.  The Galois action on the additive group of units is the Galois action on the
  units and fixes those coming from the base field, so a two-cocycle with values in `k` inflated to
  `K` satisfies the additive cocycle identity exactly when it satisfies the multiplicative one, and
  **a two-cocycle of units of the base field killed by an odd integer and locally trivial at the
  ramified finite places is the coboundary of a one-cochain of units of the extension**.
* `InverseGalois.CFT.Units.ABHNPlaces` drops the restriction on the integer.  Oddness was bought
  by the archimedean places; paying for them instead, **a two-cocycle of units of the base field
  which is locally trivial at every place, archimedean places included, is the coboundary of a
  one-cochain of units of the extension** whatever integer kills it.
* `InverseGalois.CFT.Units.ABHNLocalPower` discharges that local condition without any local
  reciprocity law.  The values of the cocycle come from the base field, so the decomposition group
  fixes them; when that group is cyclic its norm is therefore the power with exponent its order, and
  **the local condition holds as soon as each value of the cocycle is, in the completion, a power
  with that exponent of a unit fixed by the decomposition group**.
* `InverseGalois.CFT.Units.ABHNLocalNorm` sharpens that to what the cyclic case really asks.  The
  second cohomology of a cyclic group is its invariants modulo its norms, and the values of the
  cocycle are invariant, so **the local condition holds as soon as each value of the cocycle is a
  norm from the completion of the extension**, the product of its conjugates under the
  decomposition group.  A unit the group fixes has itself for every conjugate, so its norm is its
  power with exponent the order of the group and the previous condition implies this one; the
  converse fails, a ramified extension having norms that are not powers.
* `InverseGalois.CFT.Local.PrimeResidue` supplies that arithmetic when the residue field at the
  place is the prime field.  Every element of the valuation ring is then congruent to a rational
  integer, so a root of unity of order `n` reduces to an element of the multiplicative group of the
  prime field killed by `n`; that group is cyclic of order `p - 1`, so the reduction is a `d`-th
  power there as soon as `n * d` divides `p - 1`, and lifting the congruence back turns it into an
  equation.  The `d`-th root obtained is again a root of unity of order prime to the residue
  characteristic, hence fixed by every valuation preserving automorphism.
* `InverseGalois.CFT.Units.ABHNRamified` reads this at a place of a number field, where the
  decomposition group acts by valuation preserving automorphisms of the completion: **a two-cocycle
  with values in the roots of unity of the base field and killed by an odd integer is a coboundary,
  as soon as every ramified place has cyclic decomposition group, prime residue field, and residue
  characteristic congruent to one modulo the product of the order of the cocycle and the order of
  that group**.
* `InverseGalois.CFT.TotallyReal` is the other source of unramifiedness at the archimedean places.
  A ramified archimedean place is a complex place lying over a real one, so a totally real extension
  has none, and over the rationals the converse holds as well, the only place of `ℚ` being real.
  **A Galois extension of the rationals of odd degree is totally real**, and **a compositum of
  totally real intermediate fields is totally real**, so the condition is free where oddness was
  available and survives the inductions that build a field step by step.
* `InverseGalois.CFT.Units.ABHNArchimedean` removes the archimedean conditions when nothing ramifies
  there.  The decomposition group of an unramified archimedean place is trivial and a two-cochain of
  the trivial group is the differential of its only value, while a totally complex base is
  unramified at the archimedean places of every extension, so **over a totally complex base a
  two-cocycle of the units which is a coboundary at every finite place is a coboundary**; the same
  conclusion holds for **a totally real extension of an arbitrary base**, where nothing is asked of
  the order of the cocycle either.
* `InverseGalois.CFT.SqrtNegOne` is the group theory of a square root of minus one.  A field has at
  most two of them, so every automorphism either fixes a given square root `j` of minus one or
  negates it, and the subgroup fixing it is normal with two cosets; if `f` is fixed by that subgroup
  and `σ` is outside it, then `σ • f * f` is the sum of the squares of the invariant elements
  `(f + σ • f) / 2` and `(f - σ • f) / (2 * j)`.  A number field containing a square root of minus
  one is totally complex, no embedding into the real numbers being able to accommodate one, so **the
  fixed field of the subgroup is totally complex**.
* `InverseGalois.CFT.SubgroupHilbert90` transports Hilbert's theorem ninety to a subgroup.  By
  Artin's theorem a subgroup of the Galois group is the whole group of automorphisms over its own
  fixed field, over which the extension is still finite, so **a one-cocycle defined only on the
  subgroup is already the coboundary of a single unit there**.
* `InverseGalois.CFT.Units.BaseChangeCocycle` changes the base field of a two-cocycle of the units.
  The action of an automorphism on the primes of the ring of integers, on the units of the field,
  and on the units of a completion does not depend on which subfield the automorphism is taken to
  fix, so the local data cost nothing to transport, and **a torsion two-cocycle which is a
  coboundary at every ramified finite place restricts to a coboundary on any subgroup of the Galois
  group whose fixed field is totally complex**.
* `InverseGalois.CFT.Units.LocalSqrtNegOne` reads the inflated cocycle inside a completion.  The
  argument runs in the Galois group of the completion over the completion of the base rather than in
  the decomposition group, every automorphism of the completion restricting to an element of the
  latter: an invariant whose inflated cochain is a local coboundary is a norm from the invariants of
  the subgroup fixing the square root of minus one, and **such a norm is a sum of two squares in the
  completion of the base**.
* `InverseGalois.CFT.Units.LocalCoboundaryTwist` checks that correcting a cocycle by a coboundary
  disturbs nothing locally: the embedding of the units of a number field into the units of a
  completion is equivariant for the decomposition group, so **a two-cochain which is locally a
  coboundary at a finite place stays one after a twist**.
* `InverseGalois.CFT.Units.RatSumSquares` is the global counterpart.  The completion of the rational
  numbers at the prime below a prime of a number field is a field of `p`-adic numbers, and the norm
  form of the extension obtained by adjoining a square root of minus one is the sum of two squares,
  so the Hasse norm theorem gives that **a rational number which is a sum of two squares in every
  completion at a finite place is a sum of two squares**.  The real place has nothing to say, a sum
  of two squares in a single completion being already enough to make the number positive.
* `InverseGalois.CFT.Units.ABHNSqrtNegOne` spends all of this at the prime two, where over the
  rational numbers the archimedean hypothesis of the Albert-Brauer-Hasse-Noether theorem cannot be
  met, the real place ramifying in every totally complex extension.  The subgroup fixing a square
  root of minus one has a totally complex fixed field, so the theorem applies over that fixed field
  and trivialises the restriction of the cocycle; the inflation-restriction sequence in degree two
  reduces what is left to a single rational invariant; the local conditions say that this invariant
  is everywhere locally a sum of two squares, hence globally one, hence a norm from the quadratic
  subextension.  So **a two-cocycle of units of the rational numbers killed by any nonzero integer
  and locally trivial at the ramified finite places is a coboundary, as soon as the extension
  contains a square root of minus one**.
* `InverseGalois.CFT.Units.ABHNSqrtNegOneRamified` restates that with the ramified places
  discharged the way the construction verifies them, so that the presence of a square root of minus
  one replaces both the oddness of the exponent and the coprimality at the archimedean places.
* `InverseGalois.CFT.Units.TowerCoboundary` transports a local coboundary up a tower.  A place of
  the top field restricts to a place of the middle one, the decomposition group maps to the
  decomposition group there, and the embedding of one completion into the other is equivariant for
  that map, so **a two-cocycle inflated from the middle field which is a coboundary at the place
  below is a coboundary at the place above** — whether or not the place above is ramified over the
  place below, and in particular at a place the enlargement itself ramifies.
* `InverseGalois.CFT.Units.InflationDescent` brings a trivialisation back down.  If the inflation of
  a two-cocycle of the middle field to the top field is a coboundary there, then the one-cochain
  trivialising it is, up to the value of a Hilbert ninety twist, constant on the cosets of the
  kernel of the restriction map, so it descends: **a two-cocycle whose inflation is a coboundary is
  itself a coboundary**.
* `InverseGalois.CFT.Units.ABHNFinite` removes the last hypothesis.  A finite Galois extension of
  the rational numbers is the splitting field of a polynomial, and multiplying that polynomial by
  `X ^ 2 + 1` enlarges it to a finite Galois extension containing a square root of minus one.  The
  local hypothesis is free at the places of the enlarged field lying above an unramified place of
  the original one — which is what the place above two becomes — and inherited from the place below
  at the others, so the previous file applies over the enlarged field and the trivialisation
  descends: **a two-cocycle of units of the rational numbers killed by any nonzero integer and
  locally trivial at the ramified finite places is a coboundary, with no hypothesis whatever**.
* `InverseGalois.CFT.Kummer.CentralEmbedding` puts those pieces together.  The factor set of a
  section of a central extension with kernel of order `n`, transported into the units of a base
  field containing a primitive `n`-th root of unity, is a two-cocycle killed by `n`; if it is a
  coboundary at every ramified finite place then Albert-Brauer-Hasse-Noether trivialises it in the
  units of the extension, the radical descent brings the trivialising cochain back to the roots of
  unity of the base, and correcting the section by it solves the embedding problem: **a central
  embedding problem of odd prime-power kernel inside the Frattini subgroup, locally solvable at the
  ramified primes, has a proper solution over a larger extension**.  The local hypothesis is
  discharged from the statement one actually verifies in practice: a homomorphic lift of the
  restriction of the given surjection to the decomposition group at each ramified place, because the
  difference between the section and such a lift is a kernel-valued, hence central, cochain whose
  coboundary is the factor set.  It is also discharged from the arithmetic hypothesis of the
  previous file, which asks only that the decomposition group at each ramified place be cyclic and
  that the roots of unity of the base field be locally powers with exponent its order.
* `InverseGalois.CFT.Kummer.CentralEmbeddingPlaces` says the same thing over an arbitrary base
  containing the roots of unity, at the price of inspecting the archimedean places too: **a central
  embedding problem with kernel of any order inside the Frattini subgroup, solvable over the
  decomposition group at every place, has a proper solution over a larger extension**.  This is the
  local-global principle in the form that survives at the prime two, where the real places are the
  obstruction that oddness was hiding.
* `InverseGalois.CFT.Kummer.CentralEmbeddingSqrtNegOne` is the same list of criteria over an
  extension of the rational numbers, where nothing is asked at the archimedean places and nothing
  about the parity of the order of the kernel.  The congruence on the residue characteristic can
  never hold at the place above two, so the criteria are also given in a mixed form in which each
  ramified place is discharged either by a homomorphic lift over its decomposition group or by the
  congruence.
* `InverseGalois.CFT.GroupCohomology.CoprimeDescent` carries the solution back down from the
  cyclotomic field to the base.  The pullback of the two surjections defining an embedding problem
  is a central extension of the source of the given homomorphism by the kernel, a solution of the
  problem restricted to a subgroup is exactly a section of that extension over the subgroup, and the
  transfer extends such a section whenever the index of the subgroup is coprime to the order of the
  kernel; hence **an embedding problem with central kernel which is solved over a subgroup of
  coprime index is solved**, properly so when the kernel lies in the Frattini subgroup.
* `InverseGalois.CFT.GroupCohomology.CentralTwist` records the freedom left in a solution.  A
  homomorphism whose values are central may be multiplied pointwise into any homomorphism and the
  product is again a homomorphism; if in addition the values lie in the kernel of the surjection
  being lifted then **the twisted homomorphism lifts the same map**, and it is again surjective
  whenever the kernel lies in the Frattini subgroup.  Correcting a solution prime by prime by a
  character of order `ℓ` is the mechanism that turns an arbitrary solution into one whose
  ramification is controlled.
* `InverseGalois.CFT.TameFrobenius` supplies the arithmetic constraint that such a correction has to
  satisfy.  Injectivity of the tame character turns the equivariance of the tame character under
  the arithmetic Frobenius into the relation `F τ F⁻¹ = τ ^ p` inside the decomposition group; a
  homomorphism whose value at `τ` is central therefore fixes that value under the `p`-th power map,
  so **a central value killed by an integer coprime to `p - 1` is trivial**.  This is why a
  homomorphism to an `ℓ`-group can be tamely ramified only at primes congruent to one modulo `ℓ`.
* `InverseGalois.CFT.TameCyclic` records the shape of the local groups the criterion asks about.
  The tame character embeds the inertia group at a prime into the units of its residue field, a
  finite subgroup of the units of a domain, so **tame inertia is cyclic**; and Serre's
  residue-degree condition identifies the decomposition group at a ramified prime with the inertia
  group there, so **the decomposition group at a tamely ramified prime of a field satisfying that
  condition is cyclic** — exactly the hypothesis the central embedding criterion places on every
  ramified place.
* `InverseGalois.CFT.Local.PrimeResidueField` supplies the companion hypothesis on the residue
  field.  A residue degree equal to one makes the residue field an extension of the prime field of
  rank one, so the rational integers already surject onto it; combined with the density of a number
  field in its completion this gives that **at a place of residue degree one every element of the
  valuation ring of the completion differs from a rational integer by an element of valuation less
  than one**, which is what a prime residue field means for the criterion.  The same module records
  that a rational prime lying in a place has valuation the exponential of a negative integer there,
  so **the completion at a place over `p` has residue characteristic `p`**.
* `InverseGalois.CFT.Brauer.DivisionNorm` opens the study of the valuation of a division algebra.
  A single element of a finite-dimensional division algebra generates a commutative subalgebra,
  which is a field because it commutes with itself and has no zero divisors, and the norm from the
  algebra of an element of a subfield is the norm from that subfield raised to the codimension —
  a tower formula that does **not** require the subfield to be central, because left multiplication
  by an element of the subfield is the scalar action on the algebra viewed as a vector space over
  it.
* `InverseGalois.CFT.Local.SpectralNorm` identifies the unique absolute value of a finite extension
  of a complete nonarchimedean field with the field norm: `‖N_{L/K}(x)‖` is the `[L : K]`-th power
  of the spectral norm of `x`, both sides being read off the constant coefficient of the minimal
  polynomial.
* `InverseGalois.CFT.Brauer.DivisionAbsValue` combines the two: on a finite-dimensional division
  algebra over a complete nonarchimedean field, `x ↦ ‖N_{D/K}(x)‖ ^ (1 / dim)` is multiplicative,
  vanishes only at zero, extends the absolute value of the base, and — the substantial point —
  satisfies the **ultrametric inequality**, because dividing by one of the two summands puts the
  question inside the commutative subfield generated by a single element, where the quantity is the
  spectral norm.
* `InverseGalois.CFT.TateCohomology.Norm` begins the complete cohomology of an arbitrary finite
  group.  The sum of the actions of all the group elements is invariant, is unchanged by translating
  its argument, and therefore descends to a map from the coinvariants to the invariants; its
  cokernel and its kernel are the two middle groups of the complete cohomology, both annihilated by
  the order of the group, and both functorial in the representation.
* `InverseGalois.CFT.TateCohomology.Induced` shows that **both middle groups vanish for the
  functions on the group** with the translation action, since a point mass realises any prescribed
  norm and translating a point mass moves its support anywhere, and that every representation
  embeds equivariantly into those functions by recording all the translates of a vector.
* `InverseGalois.CFT.TateCohomology.Exact` builds the **six term exact sequence of the two middle
  groups** attached to a short exact sequence of representations.  Its connecting map needs no
  choice: a vector of the middle whose norm comes from the sub has a well defined preimage of that
  norm, that preimage is invariant, and the vectors with that property surject onto the norm zero
  classes of the quotient by a map whose kernel the recipe kills.
* `InverseGalois.CFT.TateCohomology.Shift` degenerates that sequence.  A representation embeds into
  the functions on the group and is a quotient of them, and both middle groups of the functions
  vanish, so the connecting map of either short exact sequence is an isomorphism: **the group in
  degree zero of a representation is the group in degree minus one of the cokernel of the
  embedding, and the group in degree minus one is the group in degree zero of the kernel of the
  summation map.**
* `InverseGalois.CFT.TateCohomology.Junction` **joins the middle groups to the ordinary cohomology
  above them.**  The connecting map of a short exact sequence out of the invariants of the quotient
  kills the norms — the norm of a lift of a vector is an invariant lift of its norm, so the cochain
  measuring the failure of the lift to be invariant vanishes — hence descends to the group in degree
  zero, and the resulting three term sequence is exact at both of its inner spots.
* `InverseGalois.CFT.TateCohomology.HomologyJunction` **joins the middle groups to the ordinary
  homology below them.**  The connecting map of a short exact sequence into the coinvariants of the
  sub lands in the classes killed by the norm, because its image in the coinvariants of the middle
  term already vanishes and the summation map of an injection is again injective on the invariants;
  the resulting three term sequence is again exact at both of its inner spots.
* `InverseGalois.CFT.TateCohomology.Graded` assembles the four ranges into **the complete
  cohomology in an arbitrary integer degree**: the ordinary cohomology above zero, the invariants
  modulo norms at zero, the norm zero classes of the coinvariants at minus one, and the ordinary
  homology of the degree shifted by one below that.  A map of representations induces a map in
  every degree and a short exact sequence has a connecting map in every degree, and the resulting
  sequence, running through all of the integers, is **exact at every one of its spots**.
* `InverseGalois.CFT.TateCohomology.Acyclic` identifies the functions on the group with the
  representation coinduced from the trivial subgroup, and deduces from Shapiro's lemma that **the
  complete cohomology of the functions on the group vanishes in every integer degree**.  A short
  exact sequence whose middle term is of that kind therefore has a **bijective connecting map in
  every degree**, which is the mechanism that shifts a statement from one degree to the next.
* `InverseGalois.CFT.TateCohomology.Shifting` presents the embedding of a representation into the
  functions on the group, and the summation onto it, as short exact sequences of representations,
  and reads off the two identifications: **the complete cohomology of the shift in a degree is the
  complete cohomology of the representation in the following degree**, and **the complete
  cohomology of a representation in a degree is the complete cohomology of its coshift in the
  following degree**.
* `InverseGalois.CFT.TateCohomology.Annihilate` runs the two inductions those identifications
  allow, upwards from degree zero and downwards from degree minus one, and concludes that **the
  order of the group annihilates the complete cohomology in every integer degree**.
* `InverseGalois.CFT.TateCohomology.Functorial` records that the map induced in a fixed degree
  takes the identity to the identity and a composite to the composite, so that **an isomorphism of
  representations induces an isomorphism of the complete cohomology** and a representation
  isomorphic to one with no complete cohomology has none either.
* `InverseGalois.CFT.TateCohomology.Transfer` builds the two middle degrees of restriction and
  corestriction from a choice of coset representatives.  Summing the actions of the
  representatives on the left factors the norm of the group through the norm of the subgroup, and
  summing on the right factors it the other way; the first sum carries invariants of the subgroup
  to invariants of the group and multiplies invariants of the group by the index, and the second
  does the same to the coinvariants, so **corestriction after restriction is multiplication by the
  index** in degree zero and in degree minus one.
* `InverseGalois.CFT.TateCohomology.Restrict` carries those two maps to every degree.  A choice of
  coset representatives splits the group as the cosets times the subgroup, so the functions on the
  group, read on the subgroup, are the functions on the subgroup with values in the functions on
  the cosets, and therefore **still have no complete cohomology**; the connecting map of either
  shifting sequence is still bijective after restriction and moves a degree.  Since the same
  connecting maps are used on both sides, **corestriction after restriction is multiplication by
  the index in every integer degree**.
* `InverseGalois.CFT.TateCohomology.SylowInjective` draws the consequence that a class killed by
  restriction to a subgroup is killed by the index of that subgroup, so that **a class killed by a
  power of a prime and by restriction to a Sylow subgroup for that prime vanishes**: the study of
  the complete cohomology of a finite group reduces to its Sylow subgroups, one prime at a time.
* `InverseGalois.CFT.TateCohomology.Iterate` repeats the shift and the coshift, so that **the
  vanishing of the complete cohomology in a single degree travels to any other degree** at the
  price of replacing the representation by an iterated shift or coshift of it.
* `InverseGalois.CFT.TateCohomology.PGroupInvariants` counts the fixed points of a `p`-group acting
  on a vector space over the field with `p` elements: the orbit of a nonzero vector spans a finite
  stable subspace of cardinality divisible by `p`, and the origin is already fixed, so **a nonzero
  representation of a `p`-group in characteristic `p` has a nonzero invariant vector**.  The same
  statement for a stable subspace and for a quotient by one follow at once.
* `InverseGalois.CFT.TateCohomology.PGroupTrivial` retracts the inclusion of the invariants and
  sends a vector to the record of its retracted translates.  That map is equivariant, and it is
  injective because its kernel is a stable subspace with no nonzero invariant vector; when the
  first cohomology vanishes it is also surjective, because a function invariant modulo the image
  produces a one-cocycle, and a one-cocycle is a coboundary.  So **a representation of a `p`-group
  in characteristic `p` with no first cohomology is the representation on the functions on the
  group**, and iterated shifting turns that into: **a representation of a `p`-group in
  characteristic `p` with no complete cohomology in one degree has none in any degree**.
* `InverseGalois.CFT.TateCohomology.PTorsionTrivial` carries that conclusion to the integers.  A
  representation over the integers all of whose vectors are killed by `p` is a representation over
  the field with `p` elements in disguise, so the inclusion of its invariants is retracted by an
  additive, hence linear, map; and both the shift and the coshift of such a representation are
  again killed by `p`.  So **a representation of a `p`-group over the integers killed by `p` with
  no complete cohomology in one degree has none in any degree**.
* `InverseGalois.CFT.TateCohomology.Additive` records that the map induced in a fixed degree is
  additive in the map of representations: in the two middle degrees this is read off from the
  description of the induced map on the invariants and on the coinvariants, and in the other
  degrees it comes from the additivity of the complex of cochains and of the complex of chains.
  Hence **a multiple of the identity of a representation induces that multiple on the complete
  cohomology** in every degree.
* `InverseGalois.CFT.TateCohomology.TorsionFree` divides a representation over the integers by the
  multiples of a prime at which it has no torsion.  The reduction is killed by that prime, so for a
  `p`-group it has no complete cohomology at all once the representation has none in two
  consecutive degrees; the long exact sequence then makes multiplication by `p` injective on the
  complete cohomology of the representation in every degree, and the order of the group, a power of
  `p`, already annihilates it.  So **a representation of a `p`-group over the integers without
  torsion at `p` whose complete cohomology vanishes in two consecutive degrees has none in any
  degree**.
* `InverseGalois.CFT.TateCohomology.CohomTrivial` removes the hypothesis on the torsion.  The free
  module on the vectors of a representation maps onto it, so the functions on the group with values
  in that free module map onto it too, and those functions have no complete cohomology; the
  connecting map therefore identifies the complete cohomology of the representation in a degree
  with that of the kernel of the surjection one degree higher.  That kernel has no torsion at all,
  being made of functions valued in a free module over the integers, so **a representation of a
  `p`-group over the integers whose complete cohomology vanishes in two consecutive degrees has
  none in any degree**.
* `InverseGalois.CFT.TateCohomology.SylowTrivial` passes from the Sylow subgroups to the whole
  group.  The order of a class divides the index of every subgroup to which the class restricts
  trivially, and a Sylow subgroup for a prime has index prime to that prime, so a class restricting
  trivially to a Sylow subgroup for every prime has an order divisible by no prime and vanishes.
  Since a Sylow subgroup is a `p`-group, **a representation over the integers whose restriction to
  a Sylow subgroup for each prime has no complete cohomology in two consecutive degrees, degrees
  that may depend on the prime, has no complete cohomology in any degree**.
* `InverseGalois.CFT.TateCohomology.AugmentationIdeal` computes the base ring with the trivial
  action.  The functions on the group are the group ring and the map summing their values is the
  augmentation, so the augmentation ideal is the coshift of the base ring and dimension shifting
  raises the degree by one.  Over the integers the norm is multiplication by the order of the
  group, which is injective, and a cocycle in degree one is a homomorphism to the integers, which
  vanishes; so **the complete cohomology of the integers vanishes in degrees minus one and one, and
  in degree zero is cyclic of order the order of the group, generated by the class of one**.
  Splicing the two identifications, **an extension of the augmentation ideal whose middle term has
  no complete cohomology at all raises the degree by two**.
* `InverseGalois.CFT.TateCohomology.CocycleExtension` twists the action of the group on the sum of
  a representation and the base ring by a cocycle in degree one: the group acts on the first
  summand through the representation, on the second trivially, and moves the second into the first
  along the cocycle.  The cocycle identity makes the twisted maps compose and the value at the
  neutral element vanishes, so **the twisted maps are a representation, an extension of the base
  ring by the given one**.  The class of one in degree zero lifts to the vector of the second
  summand and the failure of that lift to be invariant is the cocycle itself, so **the connecting
  map of the extension carries the class of one to the class of the cocycle**.
* `InverseGalois.CFT.TateCohomology.TateTheorem` is **Tate's theorem**.  Reading the twisted
  extension on a subgroup gives the extension attached to the restricted cocycle, so the connecting
  map is described there in the same way.  Suppose that on every subgroup the complete cohomology
  of the representation vanishes in degree zero, that in degree one it consists of the multiples of
  the class of the restricted cocycle, and that only the multiples of the order of the subgroup
  annihilate that class; since over the integers degree zero is cyclic of order the order of the
  group and degree one vanishes, the connecting map of the restricted extension is bijective, so
  the long exact sequence empties the middle term in degrees zero and one.  Two consecutive empty
  degrees on a Sylow subgroup for each prime empty it altogether, whence **the complete cohomology
  of the integers in a degree is the complete cohomology of the representation in the following
  degree**.
* `InverseGalois.CFT.TateCohomology.RestrictOne` reconciles the two descriptions of restriction in
  degree one.  The connecting map out of degree zero is computed on a lift of an invariant vector
  and on the cochain measuring the failure of that lift to be invariant, and restricting the lift
  and the cochain computes the connecting map of the restricted extension, so **the connecting map
  out of degree zero is natural for restriction to a subgroup**.  In the extension defining the
  shift a cocycle is its own lift, because the record of all the translates of its value at an
  element is the difference between the translate of the cocycle and the cocycle, which is the
  cocycle identity; hence **the class of a cocycle in the shift is invariant and the connecting map
  carries it to the class of the cocycle**, and **restriction in degree one carries the class of a
  cocycle to the class of the cocycle read on the subgroup**.
* `InverseGalois.CFT.TateCohomology.TateDegreeTwo` states Tate's theorem about a class in degree
  two, as it is usually met.  The degree drops by one on passing to the shift: a class in degree
  two is the class of a cocycle of the shift, since the identification raising the degree is
  surjective and every class in degree one is the class of a cocycle, and **restriction commutes
  with the identification raising the degree** by the very way restriction was defined.  So **the
  hypotheses in degrees one and two on the representation are the hypotheses in degrees zero and
  one on the shift**, and **the complete cohomology of the integers in a degree is the complete
  cohomology of the representation two degrees higher**.
* `InverseGalois.CFT.TateCohomology.Tensor` tensors two representations with the diagonal action.
  **The tensor product does not depend on the order of the factors**, and when one factor is the
  functions on the group with values in a module carrying no action the diagonal action is again
  the action by translation: a function and a vector are sent to the record, at each element of the
  group, of the value of the function there tensored with the translate of the vector by that
  element.  That comparison is an isomorphism because the tensor product distributes over a finite
  product, so **the tensor product of the functions on the group with any representation has no
  complete cohomology**.
* `InverseGalois.CFT.TateCohomology.TensorShift` moves that comparison past the shift.  Tensoring a
  cokernel with a fixed module gives the cokernel of the tensored map, and under the comparison the
  tensored embedding is the embedding of the tensor product, because the translates of a vector
  tensored with a vector are the translates of the tensor of the two vectors.  So **the shift of a
  representation tensored with another representation is the shift of the tensor product**, which
  is what lets a statement about a tensor product be moved by one degree.
* `InverseGalois.CFT.TateCohomology.TensorExtension` tensors the extension attached to a one
  cocycle.  As a module that extension is the sum of the representation and the base ring, so
  tensoring gives the sum of the tensor product and the second representation, with an element of
  the group moving a pair by acting diagonally on the first entry and adding the value of the
  cocycle tensored with the moved second entry.  **The tensored extension is again an extension**,
  of the second representation by the tensor product, and **it is the extension tensored with the
  representation**: the price usually paid to a flatness assumption is paid in advance by the
  splitting of the extension as a module.
* `InverseGalois.CFT.TateCohomology.TateNakayama` raises the degree by two with coefficients in a
  tensor product.  The connecting map of the tensored extension goes from the complete cohomology
  of a representation in a degree to that of the shift tensored with it in the following degree,
  and the shift tensored with a representation is the shift of the tensor product; so **the
  complete cohomology of a representation in a degree is the complete cohomology of its tensor
  product with the coefficients two degrees higher**, as soon as the tensored extension has no
  complete cohomology.
* `InverseGalois.CFT.TateCohomology.TensorFunctor` tensors a map of representations on the right
  with a fixed representation.  The underlying map acts on the first factor and leaves the second
  alone, and it commutes with the diagonal action because each factor is moved separately;
  composition and identities are respected factor by factor, so an isomorphism stays an isomorphism
  and a short complex stays a short complex.  Tensoring is right exact, so the map onto the
  quotient stays surjective and the image of the sub is still the whole kernel; the one thing that
  can fail is the injectivity of the map from the sub, and flatness of the fixed representation
  supplies exactly that.  So **a short exact sequence tensored with a flat representation is short
  exact**.
* `InverseGalois.CFT.TateCohomology.TensorTrivial` pays the price left over by the previous file.
  **Multiplication by a natural number commutes with tensoring**, because it may be carried out on
  either factor, so multiplication by a prime is injective on the complete cohomology of a tensor
  product as soon as the tensored reduction modulo that prime has none; over a `p`-group the order
  of the group annihilates every degree, so the tensor product has nothing anywhere.  The reduction
  of a representation with no complete cohomology is killed by `p` and has no first cohomology,
  hence is the functions on the group, which stay acyclic after tensoring; and the hypothesis of no
  torsion is removed by covering the representation with a free induced one, whose kernel has none.
  **Restriction to a subgroup commutes with tensoring**, so the argument only has to be run on the
  Sylow subgroups: **a representation whose restriction to a Sylow subgroup for every prime has no
  complete cohomology in two consecutive degrees has none after tensoring with a representation
  flat over the integers**, and **the theorem of Tate and Nakayama holds for coefficients flat over
  the integers** with no hypothesis left over.
* `InverseGalois.CFT.TateCohomology.TensorPTorsion` replaces flatness by torsion.  **A tensor
  product one of whose factors is killed by a natural number is killed by that number**, since the
  number may be moved onto that factor, and **a representation killed by a number prime to the
  order of the group has no complete cohomology**, since that order annihilates every degree too;
  so only the Sylow subgroup for that prime can carry anything.  **Reducing modulo a natural number
  becomes an isomorphism after tensoring with a representation killed by that number**: the
  reduction stays surjective by right exactness, and its kernel is the image of multiplication by
  the number, which is zero on the tensor product.  Hence **a representation whose reduction modulo
  a prime has no first cohomology on a Sylow subgroup for that prime has no complete cohomology
  after tensoring with a representation killed by that prime** -- and when the prime acts without
  torsion the reduction inherits the vanishing from the representation itself.  This gives **the
  theorem of Tate and Nakayama for coefficients killed by a prime**.
* `InverseGalois.CFT.TateCohomology.TateClassCount` turns the classical hypotheses of Tate's
  theorem into a count.  **An element of a finite commutative group annihilated by exactly the
  multiples of the order of the group generates the group**, because the subgroup of its multiples
  has as many elements as the order of the element, which the annihilator pins to the order of the
  group.  And **the restriction of a class annihilated by exactly the multiples of the order of the
  group is annihilated by exactly the multiples of the order of the subgroup**: corestriction after
  restriction is multiplication by the index, so the index times any multiple killing the
  restriction already kills the class, and the order of the group is the order of the subgroup
  times the index.  Together these say that **Tate's hypotheses on a subgroup follow from the
  vanishing of the first complete cohomology, the count of the second, and the order of the class
  over the whole group** -- the shape in which the fundamental class of a class formation presents
  itself -- and that count therefore delivers both **Tate's theorem** and **the theorem of Tate and
  Nakayama for coefficients flat over the integers** on its own.
* `InverseGalois.CFT.TateCohomology.Abelianization` names the group side of the reciprocity law.
  Below degree minus one the complete cohomology is the homology with the degree shifted by one, so
  in degree minus two it is the first homology group; the first homology group of a trivial
  representation is the abelianization of the group tensored with the coefficients, and over the
  integers the tensor factor may be dropped.  So **the complete cohomology of the trivial integral
  representation in degree minus two is the abelianization of the group**, written additively,
  which is the object Tate's theorem matches against the classes of the base modulo the norms.
* `InverseGalois.CFT.Units.IdeleClassH2` supplies the count in degree two for a cyclic
  extension.  The zeroth Tate group of the automorphism by which a generator acts is the
  quotient of the ideles of the base field by the principal ideles together with the norms, an
  index which the two inequalities pin to the degree, so **the second cohomology of the idele
  class group of a cyclic extension of number fields has exactly as many elements as the Galois
  group**.
* `InverseGalois.CFT.GroupCohomology.H2Transport` carries the second cohomology across an
  isomorphism of groups compatible with an isomorphism of modules.  A two-cocycle is transported by
  reindexing along the isomorphism, the transport of a coboundary is a coboundary, and the induced
  map on classes is a bijection because the inverse isomorphism transports back, so **the two second
  cohomology groups have the same number of elements and one is finite exactly when the other is**.
* `InverseGalois.CFT.GroupCohomology.H2Devissage` is the counting form of inflation-restriction.  A
  surjection of groups whose kernel acts on a module with an equivariant injection from a second
  module identifying it with the invariants of the kernel presents the second cohomology of the
  quotient as classes upstairs, so once the first cohomology of the kernel vanishes **the second
  cohomology of the whole group is finite and has at most as many elements as the product of the
  second cohomology of the quotient and the second cohomology of the kernel**.
* `InverseGalois.CFT.GroupCohomology.H2Sylow` assembles the count from the Sylow subgroups.  A class
  restricting to zero on every Sylow subgroup is zero, so the second cohomology embeds into the
  product over the primes dividing the order, and the orders of the Sylow subgroups multiply to the
  order of the group: **the second cohomology of a finite group is finite with at most as many
  elements as the group as soon as this holds on each of its Sylow subgroups**.
* `InverseGalois.CFT.Units.IdeleClassH2Tower` is that dévissage for a tower of number fields.
  Restriction of scalars identifies the Galois group of the top field over the middle field with the
  kernel of restriction to the middle field, and the idele classes of the middle field are exactly
  the classes fixed by that kernel, so **the number of classes for the top field over the base is at
  most the number for the middle field over the base times the number for the top field over the
  middle field**.
* `InverseGalois.CFT.Units.IdeleClassH2Full` removes the cyclicity hypothesis.  A group of
  prime-power order has a normal subgroup of prime index, so the tower dévissage and induction on
  the exponent settle every extension of prime-power degree, where the two counts multiply to
  exactly the degree; and restriction to a Sylow subgroup is the cohomology over its fixed field,
  whose degree is a prime power.  **The second cohomology of the idele class group of an arbitrary
  Galois extension of number fields is finite and has at most as many elements as the Galois
  group.**
* `InverseGalois.CFT.Units.IdeleClassTate` hands the first two of the three conditions to the idele
  class group.  The restriction of the representation to a subgroup of the Galois group is the
  representation attached to the extension over the fixed field of that subgroup, so both the
  vanishing of the first cohomology and the count of the second hold on every subgroup at once:
  **the complete cohomology of the idele class group in degree one vanishes on every subgroup, and
  in degree two it is finite with at most as many elements as the subgroup**.  What remains of the
  classical hypotheses is therefore the order of a class over the whole group, and with that in hand
  one gets **Tate's theorem for the idele class group** -- the complete cohomology of the trivial
  integral representation in a degree is that of the idele class group two degrees higher -- and
  **the theorem of Tate and Nakayama for the idele class group** for coefficients flat over the
  integers.
* `InverseGalois.CFT.Brauer.DivisionInteger` collects the first consequences of that absolute value.
  The elements of absolute value at most one form the **integers** of the algebra; the base field
  has an element whose absolute value is the largest one below one, and every absolute value of the
  base field is an integral power of it; and the square of the degree of the subalgebra generated by
  a single element is at most the dimension of the algebra, that subalgebra being a field contained
  in its own centralizer.
* `InverseGalois.CFT.Brauer.DivisionCompact` bundles the absolute value into a normed division ring
  structure.  A finite-dimensional normed space over a complete field has all of its subspaces
  closed, so **an element approximated arbitrarily well by a subspace lies in it**; and over a local
  field the space is proper, so the integers are compact and **finitely many of them meet every ball
  of radius one centred in the integers**.
* `InverseGalois.CFT.Brauer.DivisionResidue` turns that finite cover into a residue ring.  The
  congruence identifying two integers whose difference has absolute value less than one has a finite
  quotient without zero divisors, and in a finite domain the powers of a single element exhaust
  everything, so **some integer of the algebra has the property that every element of absolute value
  one differs from one of its powers by an element of absolute value less than one**.
* `InverseGalois.CFT.Brauer.DivisionValueGroup` reads the value group.  A **uniformizer** of the
  algebra is a nonzero element of absolute value less than one which is as large as it can be; one
  exists, every absolute value of the algebra is an integral power of its own, and a uniformizer of
  the base field is a power of it whose exponent — the **ramification** — is bounded by the
  dimension.
* `InverseGalois.CFT.Brauer.DivisionMaximal` pins the degree of the subfield generated by the
  residue generator.  Multiplying that subfield by the powers of a uniformizer of the algebra
  approximates every element arbitrarily well, and the span of those products is closed, so it is
  the whole algebra; comparing the bound this gives with the bound from the centralizer settles both
  at once.  **A division algebra of dimension `n * n` over a local field has an element generating a
  subfield of degree `n` whose nonzero elements have the absolute values of the nonzero scalars.**
* `InverseGalois.CFT.Brauer.DivisionSplitting` completes the local picture.  A subalgebra equal to
  its own centralizer is a field whose degree squared is the dimension, so **the dimension of a
  central division algebra is a square**, and conversely a subfield of that degree is its own
  centralizer and therefore **splits the algebra**: extending scalars to it produces a matrix
  algebra.  Applied to the subfield of the previous module this gives **a splitting field of degree
  the square root of the dimension carrying no absolute values beyond those of the base field**.
* `InverseGalois.CFT.Brauer.DivisionTeichmuller` improves the residue generator to a root of unity.
  Raising an integer congruent to one to the power `Q`, the number of residues, multiplies its
  distance to one by at most `|Q| < 1`, so the powers `y ^ (Q ^ j)` of a residue generator form a
  Cauchy sequence; the limit is a genuine root of unity of order exactly `Q - 1` congruent to the
  generator, and its powers still meet every element of absolute value one.  **A division algebra
  over a nonarchimedean local field is therefore generated over its base field by a root of unity
  of order prime to the residue characteristic.**
* `InverseGalois.CFT.Brauer.DivisionGalois` recognises that splitting field as a Galois extension.
  A subfield generated by a root of unity of order `m` is generated by the roots of `X ^ m - 1`,
  so it is a cyclotomic extension of the base field, and a cyclotomic extension is Galois.  **A
  division algebra over a nonarchimedean local field is split by a Galois subfield of degree the
  square root of the dimension carrying only the absolute values of the base field.**
* `InverseGalois.CFT.Brauer.DivisionCyclic` identifies its Galois group.  A `K`-automorphism of a
  finite extension `L` of a local field preserves the spectral norm, hence the integers, and so
  descends to the residue field of `L`; an automorphism trivial on the residues fixes the root of
  unity generating `L`, because a root of unity congruent to one is one.  The Galois group therefore
  embeds in the ring automorphisms of a finite field, which are cyclic.  **A division algebra over a
  nonarchimedean local field is split by a cyclic subfield of degree the square root of the
  dimension carrying only the absolute values of the base field.**
* `InverseGalois.CFT.Local.AdicLocalField` presents the completion of a number field at a finite
  place to that theory.  An element of the fraction field of a Dedekind domain of absolute value at
  most one differs from an element of the domain by an element of absolute value less than one: the
  ideal generated by a denominator is a power of the prime times an ideal coprime to it, so
  restoring one factor of the prime recovers the power, in which the numerator already lies.  The
  field is dense in its completion, so **the domain surjects onto the residue field of the
  completion**; hence for the ring of integers of a number field the residue field of the completion
  is finite, and since the ring of integers of the completion is a complete discrete valuation ring,
  **the completion of a number field at a finite place is a proper metric space** — a nonarchimedean
  local field in the normed sense, on which the theory of division algebras is available.
* `InverseGalois.CFT.Brauer.LocalUnramified` lifts the splitting theorem from division algebras to
  Brauer classes.  The absolute value a division algebra induces on a subfield is a multiplicative
  norm extending the absolute value of the base field, and over a complete nonarchimedean base the
  spectral norm is the only such, so **the absolute value of a division algebra restricted to a
  subfield is the spectral norm of that subfield** and the unramifiedness of the splitting field is
  a statement about the field alone.  A Brauer class is the class of a central simple algebra whose
  underlying ring is a domain, hence of a division algebra: **every Brauer class over a
  nonarchimedean local field lies in the relative Brauer group of a cyclic extension whose nonzero
  elements have the absolute values of the nonzero scalars.**
* `InverseGalois.CFT.Local.UnramifiedNormValue` reads the invariant of such an extension off the
  valuation.  When the automorphisms preserve the valuation the norm is the product of the
  conjugates, which all have the same value, so **the value of a norm is the degree-th power of a
  value**; dividing by a generator of the value group, **the invariant kills the norms.**  If the
  extension is unramified — every value of the larger field is already a value of the smaller — the
  values of the base field fill the whole value group, so **the invariant is surjective**, and when
  the norm subgroup has index the degree, as it does for a cyclic extension of complete fields,
  **the units modulo the norms are the integers modulo the degree.**
* `InverseGalois.CFT.Brauer.UnramifiedRelative` transports that to the Brauer group: the relative
  Brauer group of a cyclic extension is the units of the base field modulo the norms, so **the
  relative Brauer group of an unramified cyclic extension of local fields is the integers modulo
  the degree**, and in particular it contains a class of order the degree.
* `InverseGalois.CFT.Brauer.UnramifiedClassOrder` reaches the same class of order the degree from
  the valuation of the base field alone.  The units modulo the norms are killed by the degree,
  because the norm of a scalar is its degree-th power; and for an unramified extension the value of
  a norm is a degree-th power of a value of the base, so reading the value of a unit modulo the
  degree is a surjection onto the integers modulo the degree that kills the norms.  An element of a
  group killed by the degree whose image generates the integers modulo the degree has order exactly
  the degree, so **the relative Brauer group of an unramified cyclic extension of a discretely
  valued field contains a class of order the degree** — with no completeness, no finite residue
  field and no norm index.
* `InverseGalois.CFT.Brauer.CyclicInvariant` divides by the degree instead of reducing modulo it,
  so that the invariant of a class becomes a rational number modulo the integers rather than a
  residue modulo the degree.  The gain is that the invariant no longer remembers the extension it
  was computed with: for a tower `K ⊆ L ⊆ L'` of unramified cyclic extensions whose generators are
  compatible, the class of `(L / K, σ, a)` is the class of `(L' / K, σ', a ^ [L' : L])`, whose
  value is `[L' : L] · v(a)` and whose degree is `[L' : L] · [L : K]`, so **the two levels of the
  tower give the same invariant** and the invariants glue along a tower.
* `InverseGalois.CFT.Brauer.RealInvariant` records the archimedean member of the same family.  The
  Brauer group of the reals is cyclic of order two, so it has exactly one injection into the
  rationals modulo the integers, and **the invariant at the real place sends the class of the
  Hamilton quaternions to one half.**
* `InverseGalois.CFT.Brauer.UnramifiedAdjoin` names the generator that normalizes the choice.  In an
  unramified extension a uniformizer of the base field is already a uniformizer, so the subfield
  generated by the Teichmüller root of unity covers every residue at no cost in dimension and
  therefore **an unramified extension of a local field is generated by a root of unity** of order
  the number of nonzero residues.  An automorphism of such an extension is then determined by its
  value on that root of unity.
* `InverseGalois.CFT.Brauer.UnramifiedAut` turns that determination into an embedding.  The root of
  unity is primitive of its order, so an automorphism raises it to a power prime to that order and
  is named by the power: **the automorphism group of an unramified extension embeds into the units
  of the integers modulo the number of nonzero residues**, and in particular it is commutative.
  The Frobenius automorphism is the element of that group which raises the root of unity to the
  number of residues of the base field.
* `InverseGalois.CFT.Brauer.DivisionResidueBase` places the residues of the base field inside the
  residue ring.  The absolute value of the algebra restricts on the scalars to the absolute value of
  the base field, so **the residue field of the base field sits inside the residue ring of the
  algebra**, and the inclusion is injective because its source is a field.
* `InverseGalois.CFT.Brauer.ResidueDegree` bounds the residue field by the degree.  A relation among
  integers can be rescaled so that its coefficients are integers and at least one of them is a unit,
  and reducing the rescaled relation shows that **integers with independent residues are themselves
  independent**, so the residue field of an extension has at most as many elements as the degree of
  the extension allows.  When it has exactly that many, lifting a basis of the residue field gives a
  basis of the extension made of integers, and the absolute value of a combination of those is the
  absolute value of one of its coefficients: **an extension whose residue field is as large as the
  degree allows is unramified.**
* `InverseGalois.CFT.Brauer.RamificationIdentity` accounts for the general case, where the residue
  field is smaller than the degree allows and the missing room is taken up by the value group.  The
  absolute value of an element of a finite extension is the root of index the degree of the absolute
  value of its norm, so the absolute values of the nonzero elements are the integer powers of a
  fixed number below one and **a finite extension of a local field has a uniformizer**.  Writing the
  **ramification index** for the number of steps of the value group of the extension that make up
  one step of the value group of the base, the products of a lift of a basis of the residue field
  with the powers of a uniformizer below the ramification index form a basis: they are independent
  because the absolute value of a combination of the lifts is the absolute value of a scalar, so the
  terms of a relation have pairwise different absolute values and the largest of them cannot be
  cancelled, and they generate because such a combination corrects an element so that its absolute
  value drops by one step of the value group, while a subspace is closed for the absolute value.
  Hence **the ramification index times the residue degree is the degree of the extension.**
* `InverseGalois.CFT.Brauer.ResidueGalois` closes the gap in the other direction and names the
  Frobenius.  An unramified extension is a cyclotomic extension, hence Galois, and its automorphisms
  act faithfully on the residue field over the residue field of the base field, so the degree is at
  most the residue degree; with the previous bound **the residue degree of an unramified extension
  is its degree**.  The action on residues is therefore an isomorphism onto the Galois group of the
  residue extension, and the automorphism matching the Frobenius of the residue fields generates:
  **an unramified extension of a local field has an automorphism which generates its Galois group
  and raises every residue to the number of residues of the base field.**  Reading the two bounds in
  the other order gives the source of unramified extensions: a Galois extension generated by a root
  of unity of invertible order has as large a residue field as its degree allows, so **a cyclotomic
  extension whose order is invertible in the residue field is unramified.**
* `InverseGalois.CFT.Brauer.UnramifiedCompositum` makes the unramified extensions inside a fixed
  extension a directed family.  Each of two unramified extensions is a cyclotomic extension of
  invertible order, their compositum is a cyclotomic extension whose order is the least common
  multiple of the two orders, and that order is again invertible in the residue field: **the
  compositum of two unramified extensions of a local field is unramified.**
* `InverseGalois.CFT.Brauer.Frobenius` makes that automorphism canonical.  An extension generated by
  a root of unity of invertible order acts faithfully on its residue field, so at most one
  automorphism can raise every residue to the number of residues of the base field: **an unramified
  extension of a local field has a unique Frobenius automorphism, and it generates the Galois
  group.**
* `InverseGalois.CFT.Brauer.FrobeniusTower` propagates the normalization along a tower.  The
  absolute value of a finite extension is the spectral norm, which reads only the minimal polynomial
  over the base field, so **the absolute value of an intermediate field is the restriction of the
  absolute value of the top field**; the integers and the residues of an intermediate field
  therefore sit inside those of the top field, an intermediate field of an unramified extension is
  unramified, and **the Frobenius automorphism of the top field restricts to the Frobenius
  automorphism of the intermediate field.**
* `InverseGalois.CFT.Brauer.AdicUnramified` joins the two halves.  A rank one valuation makes a
  field into a nonarchimedean normed field whose norm determines the valuation, because the
  comparison map of a rank one valuation is strictly monotone, so the unramifiedness produced by
  the splitting theory of division algebras — every nonzero element of the splitting field has the
  absolute value of a scalar — is the same statement as the unramifiedness read off the valuation.
  Hence **every Brauer class over a complete, discretely valued, locally compact field, and in
  particular over the completion of a number field at a finite place, lies in the relative Brauer
  group of a cyclic extension whose relative Brauer group has an element of order the degree.**
* `InverseGalois.CFT.Brauer.LocalInvariant` takes the invariant with respect to the Frobenius
  automorphism, and so removes the last choice from it.  The two descriptions of unramifiedness
  agree, so the Frobenius automorphism is available as the generator, and **the invariant of a
  Brauer class split by an unramified extension of a local field attains the reciprocal of the
  degree** and **does not depend on the level of the unramified tower at which it is computed.**
* `InverseGalois.CFT.Brauer.InvariantMap` removes the choice of splitting field as well, by working
  inside a fixed algebraic closure.  Every Brauer class is split by a finite unramified extension
  there, two such extensions both sit inside their compositum, which is again unramified, and the
  invariant is unchanged on passing up a tower — an isomorphism being a tower of height one, so an
  extension isomorphic to an unramified one is unramified and has the same invariant.  Hence **the
  invariant of a Brauer class over a local field is well defined**, and **the invariants form a
  homomorphism from the whole Brauer group to the rationals modulo one** which computes the
  normalised invariant of every unramified extension.
* `InverseGalois.CFT.Brauer.InvariantInjective` shows the invariant loses nothing.  The relative
  Brauer group of an unramified extension has the order of the degree and the invariant attains the
  reciprocal of the degree, an element of that order in the rationals modulo one; a homomorphism
  out of a finite group whose image contains an element of the order of the group is injective, so
  **the invariant is injective on the relative Brauer group of an unramified extension**, and since
  every class is split by such an extension, **a Brauer class over a local field is determined by
  its invariant.**
* `InverseGalois.CFT.Brauer.InvariantSurjective` shows the invariant misses nothing either.
  Adjoining the roots of unity of order one less than a power of the number of residues is
  unramified, and those roots of unity keep their order in the residue field, so the residue field
  is at least as large as that power; one less than a power divides one less than another power
  only when the exponents divide, so **a local field has an unramified extension of degree
  divisible by any prescribed number.**  The invariant attains the reciprocal of that degree there,
  hence **every rational modulo the integers is the invariant of a Brauer class**, and with the
  previous item **the Brauer group of a local field is the rationals modulo the integers.**
* `InverseGalois.CFT.GroupCohomology.CyclicRestrict` compares the explicit cyclic two-cocycles of
  two cyclic groups joined by a homomorphism carrying a generator to the `d`-th power of a
  generator, `d` being the ratio of the orders.  Such a homomorphism multiplies discrete logarithms
  by `d`, and multiplying both sides of the comparison that defines the value of the cocycle by `d`
  leaves it unchanged, so **the explicit cyclic two-cocycle pulls back to the explicit cyclic
  two-cocycle with the same value**, on the nose rather than up to a coboundary.
* `InverseGalois.CFT.Brauer.CyclicBaseChange` reads that off on Brauer groups.  The restriction map
  is computed by restricting the defining cocycle, and the generator of the Galois group of an
  extension of an intermediate field induces a power of the generator downstairs, so **base change
  carries a cyclic algebra to a cyclic algebra with the same coefficient**, the degree of the
  intermediate field having disappeared into the change of generator.
* `InverseGalois.CFT.Brauer.InvariantRestrict` turns that into the behaviour of the invariant.  The
  coefficient is unchanged and its value is unchanged, while the degree that one divides by drops
  by the degree of the intermediate field, so **the invariant of a Brauer class is multiplied by
  the degree of the intermediate field under base change.**  A subgroup of a finite cyclic group is
  generated by the corresponding power of a generator, so **the Galois group of the top field over
  the intermediate field is generated by an automorphism inducing the power of a generator given by
  the degree of the intermediate field**, and the change of generator that the base change formula
  asks for is always available.
* `InverseGalois.CFT.Brauer.FrobeniusBaseChange` identifies that generator.  The spectral norm is
  computed from the algebra norm, which is transitive in a tower, so **the absolute value of a
  finite extension does not depend on which of two compatibly normed base fields it is computed
  over**; unramifiedness therefore passes to the intermediate field, and an automorphism raising
  every residue to the power counted by the residues of the intermediate field is the Frobenius
  automorphism there.  Iterating the Frobenius automorphism downstairs does exactly that, so **an
  automorphism inducing the power of the Frobenius automorphism given by the degree of the
  intermediate field is the Frobenius automorphism of the intermediate field.**  The two absolute
  values of the intermediate field agree, so its residues over itself are its residues over the
  base field, and **an unramified intermediate field has as many residues as the number of residues
  of the base field raised to the degree.**
* `InverseGalois.CFT.Brauer.FrobeniusRamified` treats the opposite case, a base field which has no
  more residues than the one below it.  The two absolute values of the extension still agree and
  the two Frobenius conditions ask for the same power, so **an automorphism of an extension of a
  base field with the same residues is a Frobenius automorphism over the smaller base field as soon
  as it is one over the larger**, and hence **the Frobenius automorphism of an unramified extension
  of the larger base field restricts to the Frobenius automorphism of an unramified extension of
  the smaller one inside it.**
* `InverseGalois.CFT.Brauer.LocalInvariantRestrict` normalises the base-change formula.  Both
  invariants are taken with respect to the Frobenius automorphism, and the Frobenius automorphism
  of the top field over the intermediate field is precisely an automorphism inducing the power of
  the Frobenius automorphism downstairs given by the degree, so the change of generator that the
  base-change formula for cyclic algebras asks for is the change of normalisation: **the normalised
  invariant of a Brauer class over a local field is multiplied by the degree of a compatibly normed
  unramified intermediate field under base change.**
* `InverseGalois.CFT.Brauer.CyclicCompositum` runs the same computation along a field that need not
  be intermediate.  An isomorphism of Galois groups carrying a generator to a generator preserves
  discrete logarithms and the two orders agree, so the explicit cyclic two-cocycle transports on the
  nose, and **base change along a field that is not intermediate carries a cyclic algebra to a
  cyclic algebra with the same coefficient**; no power of the generator appears.
* `InverseGalois.CFT.Brauer.InvariantCompositum` reads off the invariant.  The coefficient and the
  degree are both unchanged, so only the value of the coefficient can move, and **the invariant of a
  Brauer class is multiplied by the factor by which the value of the base field is multiplied.**
* `InverseGalois.CFT.Local.NormValued` carries the whole local package up a finite extension.  The
  value of the field norm is a valuation on the extension, because the norm of an element is the
  degree-th power of its spectral norm and the spectral norm is nonarchimedean; carried on the
  uniformity of the spectral norm it is a topological valuation, since a set is a neighbourhood of
  zero exactly when it contains a ball, so **a finite extension of a complete, discretely valued,
  locally compact field is again one**.  The field norm is invariant under the automorphisms over
  the base by transport of structure, so **the automorphisms preserve the valuation**; the residue
  characteristic multiplies by the degree; and a valuation ring of a proper metric space is a
  compact set whose next step is open, so its quotient is discrete and compact, hence **the graded
  pieces are finite** — with no uniformizer of the extension needed.
* `InverseGalois.CFT.Brauer.LocalBrauerOrder` puts the going-up together with the counting.  The
  cyclic splitting field produced by the theory of division algebras is unramified, hence a local
  field again, so its relative Brauer group is the units of the base field modulo the norms, which
  is the integers modulo the degree: **every Brauer class over a complete, discretely valued,
  locally compact field, and in particular over the completion of a number field at a finite place,
  lies in a relative Brauer group of exactly the order of the degree.**
* `InverseGalois.CFT.Units.CompositumEmbed` transports a fundamental class from one extension of the
  rationals to another of the same degree.  The kernel of the restriction of automorphisms to a
  subfield is the subgroup fixing that subfield pointwise, so two embeddings with intersection the
  rationals and compositum the whole top field have complementary, jointly trivial kernels, and the
  Galois group of the compositum is the product of the two groups; the cyclic computation upstairs
  and the two restrictions therefore agree on orders, so **a class of the right order in the second
  cohomology of the idele class group of a cyclic extension produces one for any other extension of
  the same degree disjoint from it.**
* `InverseGalois.CFT.Units.GlobalFundamental` supplies the disjoint partner unconditionally.  A
  prime larger than the degree, congruent to one modulo twice the degree and splitting completely in
  the given extension exists by Dirichlet, and the cyclotomic field of that conductor contains a
  cyclic totally real subfield of exactly the degree, totally ramified there and unramified
  elsewhere; the two are disjoint because ramification cannot survive complete splitting, and the
  same complete splitting makes the generating idele a norm because the automorphisms permute the
  places above the prime freely.  Hence **the second cohomology of the idele class group of an
  arbitrary Galois extension of the rationals contains a class annihilated by exactly the multiples
  of the degree**, which is the last of the three conditions defining a class formation.
* `InverseGalois.CFT.Units.GlobalTate` names that class and reaps the consequences.  With the
  vanishing of the first cohomology and the bound on the second already known for every subgroup,
  **Tate's theorem holds for the idele class group of any Galois extension of the rationals with no
  hypotheses**, identifying its complete cohomology in every degree with that of the trivial
  integral representation two degrees lower; in degree minus two this is **the reciprocity
  isomorphism**, and tensoring gives **the theorem of Tate and Nakayama** for any coefficients flat
  over the integers.
* `InverseGalois.CFT.Units.BaseFundamental` moves the base field off the rationals, by restriction
  and then inflation.  An intermediate field of an extension Galois over the rationals corresponds
  to the image of restriction of scalars, which is an injective homomorphism of Galois groups, and
  the class over the rationals restricts along it to a class annihilated by exactly the multiples
  of the order of that subgroup, which is the degree over the intermediate field; the two
  representations agree because enlarging the base does not change how an automorphism moves an
  idele.  A Galois extension of that base is then the quotient of its normal closure over the
  rationals by a subgroup whose order annihilates every complete cohomology group, so that multiple
  of the class restricts to zero and is inflated from the quotient, and the dévissage for a tower
  turns the inflated class into one downstairs.  Hence **the second cohomology of the idele class
  group of a Galois extension of number fields contains a class annihilated by exactly the
  multiples of the degree**, with no hypothesis on the base.
* `InverseGalois.CFT.Units.BaseTate` names that class and reaps the consequences over an arbitrary
  base.  The vanishing of the first cohomology and the bound on the second were never special to
  the rationals, so with the fundamental class in hand **Tate's theorem holds for the idele class
  group of any Galois extension of number fields with no hypotheses**, identifying its complete
  cohomology in every degree with that of the trivial integral representation two degrees lower;
  degree minus two is **the reciprocity isomorphism** of the extension, and tensoring gives **the
  theorem of Tate and Nakayama** for any coefficients flat over the integers.
* `InverseGalois.CFT.Units.BaseArtin` puts a name on the left hand side of that identification.
  Composing it with the description of the complete cohomology of the trivial integral
  representation in degree minus two gives **the reciprocity isomorphism between the abelianization
  of the Galois group of an extension of number fields and the complete cohomology of the idele
  class group in degree zero**, the invariant idele classes modulo the norms from the extension.
* `InverseGalois.CFT.Profinite.Cochain` is the cohomology of a topological group in degrees one and
  two, computed by the cochains that factor through a quotient by an open normal subgroup.  Those
  cochains are closed under the group operations and under the coboundary, so the cocycles form a
  group and the coboundaries a subgroup of it, and the quotient is the cohomology; an action for
  which some open normal subgroup acts trivially takes a smooth cochain to a smooth coboundary,
  which is what makes the two subgroups sit inside one another.  Because the topology of a finite
  Galois group is discrete, a finite level and an infinite one are described in the same language.
* `InverseGalois.CFT.Profinite.Comap` composes a cochain with a homomorphism into a group acting on
  the same module.  The cocycle relation and the coboundary are both preserved because the two
  actions agree, so all that is needed is that composition preserve smoothness, and two conditions
  give that: a continuous homomorphism pulls an open normal subgroup back to one, and a
  homomorphism with open kernel pulls every subgroup back to one containing that kernel, which
  makes even a cochain that was not smooth become smooth.  So **there is a homomorphism of the
  cohomology of the target into that of the source**, in degree one and in degree two, computed on
  cocycles; the first condition is restriction to a closed subgroup and the second is inflation
  from a finite level.
* `InverseGalois.CFT.Profinite.InfRes` reads off what smoothness alone forces.  A smooth one
  cocycle is trivial on the subgroup it is smooth for, and the values of a smooth cocycle in either
  degree are fixed by that subgroup, so a cocycle constant on the cosets of the kernel of a
  surjection is literally a cocycle of the quotient composed with the projection.  In degree one
  that gives both halves of inflation and restriction that get used: **inflation is injective**,
  because a one cochain of the quotient which becomes a coboundary upstairs was already the
  coboundary of the same element, and **a class whose restriction to the kernel is trivial is
  inflated**, because correcting by that coboundary makes the cocycle trivial on the kernel and
  hence constant on its cosets.  In degree two the same reading gives **every class represented at
  a level is inflated from it.**
* `InverseGalois.CFT.Profinite.Quotient` names a *level*: an open normal subgroup which acts
  trivially on the coefficients.  The quotient by it acts, and is discrete, and the projection to it
  has open kernel, so composing with the projection is **inflation from that level**, injective in
  degree one and hitting every class represented there in either degree.  The levels are cofinal for
  a trivial reason: smoothness of a cochain is constancy on the cosets of an open normal subgroup
  and smoothness of the action is triviality on one, and the intersection of the two is again open
  and normal, so **every class of either degree is represented at a level.**
* `InverseGalois.CFT.Profinite.Krull` reads that dictionary on the Galois group of an arbitrary
  Galois extension, whose topology has the subgroups fixing a finite Galois intermediate field for a
  basis at the identity.  Such a subgroup is the kernel of restriction to that field, hence open and
  normal, and restriction is surjective, so **restriction to a finite Galois level is inflation**;
  conversely an open subgroup is a neighbourhood of the identity and so contains one of them, which
  makes the finite Galois levels cofinal and gives **every class of the first or second cohomology
  of an infinite Galois group a representative at a finite Galois level.**
* `InverseGalois.CFT.Profinite.Res` goes the other way, along the inclusion of a subgroup: the
  subspace topology makes the inclusion continuous and the subgroup inherits smoothness of the
  action, so composing a cochain with it is **restriction to that subgroup**, and its triviality
  says the representing cocycle is a coboundary there.  A family of subgroups then cuts out the
  classes dying on every member of it, the shape in which the everywhere locally trivial classes of
  a number field appear once a place is read as a decomposition subgroup.
* `InverseGalois.CFT.Profinite.Trivial` is the case of coefficients on which the group acts
  trivially, the one that carries the local-global arguments.  There the cocycle relation says
  exactly that the cochain is a homomorphism, every coboundary is trivial, and smoothness is
  openness of the kernel, so **a class dies on a family of subgroups exactly when every one of them
  lies in the kernel of the corresponding homomorphism.**
* `InverseGalois.CFT.Profinite.Cup` multiplies two one cochains into a two cochain along a pairing
  of the coefficients.  The cocycle relation in degree two is the pairing of the two relations in
  degree one, and smoothness is inherited from a subgroup smoothing both factors and acting
  trivially on the target, so **there is a cup product of first cohomology into second**; it
  commutes with composing along a homomorphism, hence with restriction, so **a class whose either
  factor dies everywhere locally is itself everywhere locally trivial.**
* `InverseGalois.CFT.Profinite.Hilbert90` is the arithmetic input.  A smooth cocycle is constant on
  the cosets of the subgroup fixing a finite Galois level and its values are fixed by that
  subgroup, hence lie in the level, so choosing a preimage of each automorphism of the level turns
  it into a cocycle there, where Noether's theorem supplies a primitive; every automorphism acts on
  the level through its restriction, so the same primitive works upstairs.  Thus **a smooth one
  cocycle with values in the units of the extension is a coboundary**, and the first cohomology of
  an infinite Galois group with those coefficients is trivial.
* `InverseGalois.CFT.Profinite.Kummer` is what that triviality computes.  When the base contains a
  primitive root of unity of the relevant order, a root of a unit of the base has a coboundary
  whose values are roots of unity of the base, and an element of the extension is fixed by the
  subgroup fixing the normal closure of the field it generates, so **the coboundary of a radical is
  a smooth one cocycle with roots of unity as coefficients**; conversely Hilbert's theorem ninety
  produces a radical from such a cocycle, whose power is fixed by everything and so lies in the
  base.  A class is trivial exactly when the radicand is already a power there, because two roots
  of the same element differ by a root of unity of the base.
-/
