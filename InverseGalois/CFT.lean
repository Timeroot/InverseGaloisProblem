import InverseGalois.CFT.Approximation.Basic
import InverseGalois.CFT.Approximation.Completion
import InverseGalois.CFT.Approximation.Places
import InverseGalois.CFT.Approximation.PowClass
import InverseGalois.CFT.BaseCompositum
import InverseGalois.CFT.BaseRamification
import InverseGalois.CFT.BaseTotallyRamified
import InverseGalois.CFT.Brauer.AdicUnramified
import InverseGalois.CFT.Brauer.BaseChange
import InverseGalois.CFT.Brauer.BaseChangeCentralizer
import InverseGalois.CFT.Brauer.BaseCyclicClass
import InverseGalois.CFT.Brauer.BaseCyclotomic
import InverseGalois.CFT.Brauer.BaseOddReciprocity
import InverseGalois.CFT.Brauer.BaseReciprocity
import InverseGalois.CFT.Brauer.BaseSignCorrector
import InverseGalois.CFT.Brauer.BaseSubcyclotomic
import InverseGalois.CFT.Brauer.BaseSubcyclotomicSplit
import InverseGalois.CFT.Brauer.Centralizer
import InverseGalois.CFT.Brauer.CentralizerProduct
import InverseGalois.CFT.Brauer.CrossedProduct
import InverseGalois.CFT.Brauer.CrossedProductCohomologous
import InverseGalois.CFT.Brauer.CrossedProductCompositum
import InverseGalois.CFT.Brauer.CrossedProductInflate
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
import InverseGalois.CFT.Brauer.CyclicGenerator
import InverseGalois.CFT.Brauer.CyclicInvariant
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Brauer.CyclicNormResidue
import InverseGalois.CFT.Brauer.CyclicProduct
import InverseGalois.CFT.Brauer.CyclicTower
import InverseGalois.CFT.Brauer.CyclicTransport
import InverseGalois.CFT.Brauer.CyclotomicFrobenius
import InverseGalois.CFT.Brauer.CyclotomicGenerator
import InverseGalois.CFT.Brauer.DecompositionTransfer
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
import InverseGalois.CFT.Brauer.FibreConductor
import InverseGalois.CFT.Brauer.FibreExponent
import InverseGalois.CFT.Brauer.FibreInvariant
import InverseGalois.CFT.Brauer.FibreTotal
import InverseGalois.CFT.Brauer.Frobenius
import InverseGalois.CFT.Brauer.FrobeniusBaseChange
import InverseGalois.CFT.Brauer.FrobeniusRamified
import InverseGalois.CFT.Brauer.FrobeniusTower
import InverseGalois.CFT.Brauer.GaloisSplitting
import InverseGalois.CFT.Brauer.Group
import InverseGalois.CFT.Brauer.H2Brauer
import InverseGalois.CFT.Brauer.H2Surjective
import InverseGalois.CFT.Brauer.HasseNoether
import InverseGalois.CFT.Brauer.HasseNorm
import InverseGalois.CFT.Brauer.InertiaDegRat
import InverseGalois.CFT.Brauer.InertiaSubfield
import InverseGalois.CFT.Brauer.InfiniteCyclic
import InverseGalois.CFT.Brauer.InfiniteInvariant
import InverseGalois.CFT.Brauer.InfinitePlaceCrossedProduct
import InverseGalois.CFT.Brauer.InflateTower
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
import InverseGalois.CFT.Brauer.LocalReciprocityAll
import InverseGalois.CFT.Brauer.LocalSymbol
import InverseGalois.CFT.Brauer.LocalSymbolRamified
import InverseGalois.CFT.Brauer.LocalSymbolUnits
import InverseGalois.CFT.Brauer.TameEvaluation
import InverseGalois.CFT.Brauer.TameSymbol
import InverseGalois.CFT.Brauer.TameOdd
import InverseGalois.CFT.Brauer.TamePower
import InverseGalois.CFT.Brauer.TameResidue
import InverseGalois.CFT.Brauer.TameValue
import InverseGalois.CFT.Brauer.LocalUnramified
import InverseGalois.CFT.Brauer.MaximalSubfield
import InverseGalois.CFT.Brauer.NormAdjust
import InverseGalois.CFT.Brauer.NormFactors
import InverseGalois.CFT.Brauer.NormPlaceValue
import InverseGalois.CFT.Brauer.NormPrimesOver
import InverseGalois.CFT.Brauer.NormReduction
import InverseGalois.CFT.Brauer.OddArchimedean
import InverseGalois.CFT.Brauer.OddArchimedeanBase
import InverseGalois.CFT.Brauer.Opposite
import InverseGalois.CFT.Brauer.PlaceCoboundary
import InverseGalois.CFT.Brauer.PlaceCrossedProduct
import InverseGalois.CFT.Brauer.PlaceCyclic
import InverseGalois.CFT.Brauer.PlaceConductor
import InverseGalois.CFT.Brauer.PlaceConductorBase
import InverseGalois.CFT.Brauer.PlaceCyclotomic
import InverseGalois.CFT.Brauer.PlaceExponent
import InverseGalois.CFT.Brauer.PlaceFrobenius
import InverseGalois.CFT.Brauer.PlaceFrobeniusDegree
import InverseGalois.CFT.Brauer.PlaceInvariant
import InverseGalois.CFT.Brauer.PlaceInvariantFinite
import InverseGalois.CFT.Brauer.PlaceOrders
import InverseGalois.CFT.Brauer.PlaceRadical
import InverseGalois.CFT.Brauer.PlaceRamified
import InverseGalois.CFT.Brauer.PlaceRamifiedAut
import InverseGalois.CFT.Brauer.PlaceSubcyclotomic
import InverseGalois.CFT.Brauer.PlaceSubcyclotomicBase
import InverseGalois.CFT.Brauer.PlaceSubcyclotomicFibre
import InverseGalois.CFT.Brauer.PlaceSubcyclotomicPower
import InverseGalois.CFT.Brauer.PlaceTotallyRamified
import InverseGalois.CFT.Brauer.PlaceUnitValue
import InverseGalois.CFT.Brauer.PlaceUnramified
import InverseGalois.CFT.Brauer.PrescribedValue
import InverseGalois.CFT.Brauer.Primary
import InverseGalois.CFT.Brauer.QuadraticExt
import InverseGalois.CFT.Brauer.Quaternion
import InverseGalois.CFT.Brauer.RamificationIdentity
import InverseGalois.CFT.Brauer.RadicalInvariant
import InverseGalois.CFT.Brauer.RadicalLevel
import InverseGalois.CFT.Brauer.RatBase
import InverseGalois.CFT.Brauer.RatCount
import InverseGalois.CFT.Brauer.RatReciprocity
import InverseGalois.CFT.Brauer.RatResidueOrder
import InverseGalois.CFT.Brauer.RationalBrauer
import InverseGalois.CFT.Brauer.RelativeCyclic
import InverseGalois.CFT.Brauer.RelativeHasse
import InverseGalois.CFT.Brauer.RelativeIndex
import InverseGalois.CFT.Brauer.RelativeTorsion
import InverseGalois.CFT.Brauer.RealBrauer
import InverseGalois.CFT.Brauer.RealCorrector
import InverseGalois.CFT.Brauer.RealCyclicSign
import InverseGalois.CFT.Brauer.RealInvariant
import InverseGalois.CFT.Brauer.RealPlace
import InverseGalois.CFT.Brauer.ResidueBaseChange
import InverseGalois.CFT.Brauer.ResidueCard
import InverseGalois.CFT.Brauer.ResidueCardDegree
import InverseGalois.CFT.Brauer.ResidueCongruence
import InverseGalois.CFT.Brauer.ResidueDegree
import InverseGalois.CFT.Brauer.ResidueGalois
import InverseGalois.CFT.Brauer.ResidueGenerator
import InverseGalois.CFT.Brauer.Semilinear
import InverseGalois.CFT.Brauer.SkolemNoether
import InverseGalois.CFT.Brauer.SmoothBrauer
import InverseGalois.CFT.Brauer.SmoothInvariant
import InverseGalois.CFT.Brauer.SmoothLevel
import InverseGalois.CFT.Brauer.SolvableBound
import InverseGalois.CFT.Brauer.SolvableNormBound
import InverseGalois.CFT.Brauer.Split
import InverseGalois.CFT.Brauer.SplitBase
import InverseGalois.CFT.Brauer.SplitLocalDegree
import InverseGalois.CFT.Brauer.SplittingSubfield
import InverseGalois.CFT.Brauer.SubcyclotomicCorrector
import InverseGalois.CFT.Brauer.SubcyclotomicReciprocity
import InverseGalois.CFT.Brauer.SubcyclotomicSplit
import InverseGalois.CFT.Brauer.SymbolCyclicAlgebra
import InverseGalois.CFT.Brauer.SymbolNorm
import InverseGalois.CFT.Brauer.SymbolSteinberg
import InverseGalois.CFT.Brauer.TensorSimple
import InverseGalois.CFT.Brauer.TotalInvariant
import InverseGalois.CFT.Brauer.TotallyRealInvariant
import InverseGalois.CFT.Brauer.TotallyRealInvariantBase
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
import InverseGalois.CFT.Cyclotomic.AuxiliarySubfield
import InverseGalois.CFT.Cyclotomic.BuildingBlock
import InverseGalois.CFT.Cyclotomic.Chebotarev
import InverseGalois.CFT.Cyclotomic.CyclicSubfield
import InverseGalois.CFT.Cyclotomic.CyclotomicInertiaDeg
import InverseGalois.CFT.Cyclotomic.DivisorSubfield
import InverseGalois.CFT.Cyclotomic.EighthRootSubfield
import InverseGalois.CFT.Cyclotomic.Frobenius
import InverseGalois.CFT.Cyclotomic.FrobeniusSplitting
import InverseGalois.CFT.Cyclotomic.ImaginarySubfield
import InverseGalois.CFT.Cyclotomic.InertiaOrder
import InverseGalois.CFT.Cyclotomic.OnePrimeRamified
import InverseGalois.CFT.Cyclotomic.PrimeSelection
import InverseGalois.CFT.Cyclotomic.QuadraticSubfield
import InverseGalois.CFT.Cyclotomic.Ramified
import InverseGalois.CFT.Cyclotomic.Splitting
import InverseGalois.CFT.Cyclotomic.SquareRoots
import InverseGalois.CFT.Cyclotomic.SubfieldFrobenius
import InverseGalois.CFT.Cyclotomic.SubfieldNorm
import InverseGalois.CFT.Cyclotomic.TotallyRamified
import InverseGalois.CFT.Cyclotomic.TotallyRealSubfield
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Decomposition
import InverseGalois.CFT.Disjoint
import InverseGalois.CFT.FibreCompositum
import InverseGalois.CFT.FrobeniusInvolution
import InverseGalois.CFT.FrobeniusStabilizer
import InverseGalois.CFT.GaloisDescent
import InverseGalois.CFT.GroupCohomology.AbelianLift
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
import InverseGalois.CFT.GroupCohomology.MapInjective
import InverseGalois.CFT.GroupCohomology.OfCocycle
import InverseGalois.CFT.GroupCohomology.SylowRes
import InverseGalois.CFT.GroupCohomology.TateTwist
import InverseGalois.CFT.GroupCohomology.ToCocycle
import InverseGalois.CFT.GroupCohomology.Transgression
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
import InverseGalois.CFT.Kummer.DecompositionLocalPower
import InverseGalois.CFT.Kummer.Denominator
import InverseGalois.CFT.Kummer.DyadicInertiaChar
import InverseGalois.CFT.Kummer.DyadicPlace
import InverseGalois.CFT.Kummer.DyadicSquareClass
import InverseGalois.CFT.Kummer.GlobalPower
import InverseGalois.CFT.Kummer.InertiaBound
import InverseGalois.CFT.Kummer.InfiniteLevelPower
import InverseGalois.CFT.Kummer.InflationRootsOfUnity
import InverseGalois.CFT.Kummer.LevelOne
import InverseGalois.CFT.Kummer.LocalPowRepresentatives
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.Kummer.LocalPowerRange
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
import InverseGalois.CFT.Kummer.SupKummerData
import InverseGalois.CFT.Kummer.SupPowSurjective
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
import InverseGalois.CFT.Local.CyclotomicRadical
import InverseGalois.CFT.Local.CyclotomicUniformiser
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
import InverseGalois.CFT.Local.GaussNorm
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
import InverseGalois.CFT.Local.KummerIrreducible
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
import InverseGalois.CFT.Local.RadicalUnramified
import InverseGalois.CFT.Local.RamifiedNormForm
import InverseGalois.CFT.Local.RatResidueDegree
import InverseGalois.CFT.Local.RatUniformiser
import InverseGalois.CFT.Local.ResidueDiscreteLog
import InverseGalois.CFT.Local.ResiduePrimitiveRoot
import InverseGalois.CFT.Local.ResidueRootUnity
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
import InverseGalois.CFT.PoitouTate.CupDual
import InverseGalois.CFT.PoitouTate.Dual
import InverseGalois.CFT.PoitouTate.ShaSurjection
import InverseGalois.CFT.PoitouTate.ShaTate
import InverseGalois.CFT.PrimeProductSquare
import InverseGalois.CFT.Profinite.Cochain
import InverseGalois.CFT.Profinite.Coeff
import InverseGalois.CFT.Profinite.Comap
import InverseGalois.CFT.Profinite.Cup
import InverseGalois.CFT.Profinite.Discrete
import InverseGalois.CFT.Profinite.FixingSubgroup
import InverseGalois.CFT.Profinite.H1Conj
import InverseGalois.CFT.Profinite.Hilbert90
import InverseGalois.CFT.Profinite.InfRes
import InverseGalois.CFT.Profinite.Kummer
import InverseGalois.CFT.Profinite.KummerConj
import InverseGalois.CFT.Profinite.KummerAction
import InverseGalois.CFT.Profinite.KummerFinite
import InverseGalois.CFT.Profinite.KummerHom
import InverseGalois.CFT.Profinite.KummerLevel
import InverseGalois.CFT.Profinite.KummerLevelDegree
import InverseGalois.CFT.Profinite.KummerLocal
import InverseGalois.CFT.Profinite.KummerLocalCompare
import InverseGalois.CFT.Profinite.KummerLocalQuot
import InverseGalois.CFT.Profinite.KummerLocalSurjective
import InverseGalois.CFT.Profinite.KummerLocalTate
import InverseGalois.CFT.Profinite.KummerRep
import InverseGalois.CFT.Profinite.KummerRes
import InverseGalois.CFT.Profinite.KummerTower
import InverseGalois.CFT.Profinite.KummerTransport
import InverseGalois.CFT.Profinite.KummerTwist
import InverseGalois.CFT.Profinite.KummerTwo
import InverseGalois.CFT.Profinite.Pi
import InverseGalois.CFT.Profinite.PiTwo
import InverseGalois.CFT.Profinite.Quotient
import InverseGalois.CFT.Profinite.QuotientAction
import InverseGalois.CFT.Profinite.Krull
import InverseGalois.CFT.Profinite.Res
import InverseGalois.CFT.Profinite.ShaComap
import InverseGalois.CFT.Profinite.Symbol
import InverseGalois.CFT.Profinite.SymbolCyclic
import InverseGalois.CFT.Profinite.Transgression
import InverseGalois.CFT.Profinite.TransgressionClass
import InverseGalois.CFT.Profinite.TransgressionInflate
import InverseGalois.CFT.Profinite.TransgressionRestrict
import InverseGalois.CFT.Profinite.Trivial
import InverseGalois.CFT.Profinite.Twist
import InverseGalois.CFT.Profinite.TwistAction
import InverseGalois.CFT.Profinite.TwistConj
import InverseGalois.CFT.Profinite.TwistRes
import InverseGalois.CFT.Profinite.TwistTensor
import InverseGalois.CFT.RatUnits
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
import InverseGalois.CFT.Scholz.AuxPrimeFamily
import InverseGalois.CFT.Scholz.AuxPrimeField
import InverseGalois.CFT.Scholz.AuxPrimePair
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
import InverseGalois.CFT.Scholz.DyadicAuxPrime
import InverseGalois.CFT.Scholz.DyadicAuxPrimeFamily
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
import InverseGalois.CFT.Scholz.QuarticRadical
import InverseGalois.CFT.Scholz.RadicalDegree
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
import InverseGalois.CFT.Scholz.TwoPowerRadical
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
import InverseGalois.CFT.Tate.FamilyCoboundaryOne
import InverseGalois.CFT.Tate.FamilyCoind
import InverseGalois.CFT.Tate.FamilyConst
import InverseGalois.CFT.Tate.FamilyFree
import InverseGalois.CFT.Tate.FamilyH1Local
import InverseGalois.CFT.Tate.FamilyInvariant
import InverseGalois.CFT.Tate.FamilyNorm
import InverseGalois.CFT.Tate.FamilyOrbit
import InverseGalois.CFT.Tate.FamilyOrbits
import InverseGalois.CFT.Tate.FamilyProduct
import InverseGalois.CFT.Tate.FamilyReindex
import InverseGalois.CFT.Tate.FamilyResGroup
import InverseGalois.CFT.Tate.FamilyRestrict
import InverseGalois.CFT.Tate.FamilyRestrictCoind
import InverseGalois.CFT.Tate.FamilyRestrictOrbit
import InverseGalois.CFT.Tate.FamilyRing
import InverseGalois.CFT.Tate.FamilySigma
import InverseGalois.CFT.Tate.FamilyTensor
import InverseGalois.CFT.Tate.FamilyTensorFinsupp
import InverseGalois.CFT.Tate.FamilyTensorFull
import InverseGalois.CFT.Tate.FamilyTensorLocal
import InverseGalois.CFT.Tate.FamilyTensorOrbit
import InverseGalois.CFT.Tate.FamilyTorsion
import InverseGalois.CFT.Tate.FamilyTrunc
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
import InverseGalois.CFT.Tate.LiftInvariants
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
import InverseGalois.CFT.Tate.ProdH1
import InverseGalois.CFT.Tate.QuotientFixed
import InverseGalois.CFT.Tate.RealBasis
import InverseGalois.CFT.Tate.RealForm
import InverseGalois.CFT.Tate.RealHerbrand
import InverseGalois.CFT.Tate.Restrict
import InverseGalois.CFT.Tate.Shapiro
import InverseGalois.CFT.Tate.Surjection
import InverseGalois.CFT.Tate.TensorSplit
import InverseGalois.CFT.Tate.TorsionRep
import InverseGalois.CFT.Tate.Trivial
import InverseGalois.CFT.Tate.TrivialLattice
import InverseGalois.CFT.TateCohomology.Abelianization
import InverseGalois.CFT.TateCohomology.Acyclic
import InverseGalois.CFT.TateCohomology.Additive
import InverseGalois.CFT.TateCohomology.Annihilate
import InverseGalois.CFT.TateCohomology.AugmentationIdeal
import InverseGalois.CFT.TateCohomology.CocycleExtension
import InverseGalois.CFT.TateCohomology.CohomTrivial
import InverseGalois.CFT.TateCohomology.Cyclic
import InverseGalois.CFT.TateCohomology.CyclicDual
import InverseGalois.CFT.TateCohomology.CyclicVanishing
import InverseGalois.CFT.TateCohomology.DeltaCoshift
import InverseGalois.CFT.TateCohomology.DeltaNatural
import InverseGalois.CFT.TateCohomology.DeltaRetract
import InverseGalois.CFT.TateCohomology.DeltaShift
import InverseGalois.CFT.TateCohomology.Duality
import InverseGalois.CFT.TateCohomology.DualityDivisible
import InverseGalois.CFT.TateCohomology.DualityFinite
import InverseGalois.CFT.TateCohomology.DualityNatural
import InverseGalois.CFT.TateCohomology.DualityShift
import InverseGalois.CFT.TateCohomology.Exact
import InverseGalois.CFT.TateCohomology.FreePresentation
import InverseGalois.CFT.TateCohomology.Functorial
import InverseGalois.CFT.TateCohomology.Graded
import InverseGalois.CFT.TateCohomology.GroupCongr
import InverseGalois.CFT.TateCohomology.HomologyJunction
import InverseGalois.CFT.TateCohomology.Induced
import InverseGalois.CFT.TateCohomology.Iterate
import InverseGalois.CFT.TateCohomology.Junction
import InverseGalois.CFT.TateCohomology.NakayamaCoeff
import InverseGalois.CFT.TateCohomology.NakayamaNatural
import InverseGalois.CFT.TateCohomology.NakayamaNextNatural
import InverseGalois.CFT.TateCohomology.NakayamaNextRestrict
import InverseGalois.CFT.TateCohomology.NakayamaRestrict
import InverseGalois.CFT.TateCohomology.NakayamaSubgroup
import InverseGalois.CFT.TateCohomology.NakayamaSubgroupError
import InverseGalois.CFT.TateCohomology.Norm
import InverseGalois.CFT.TateCohomology.PGroupInvariants
import InverseGalois.CFT.TateCohomology.PGroupTrivial
import InverseGalois.CFT.TateCohomology.PTorsionTrivial
import InverseGalois.CFT.TateCohomology.Pair
import InverseGalois.CFT.TateCohomology.Pontryagin
import InverseGalois.CFT.TateCohomology.Product
import InverseGalois.CFT.TateCohomology.Restrict
import InverseGalois.CFT.TateCohomology.RestrictDelta
import InverseGalois.CFT.TateCohomology.RestrictNatural
import InverseGalois.CFT.TateCohomology.RestrictShift
import InverseGalois.CFT.TateCohomology.RestrictShiftBridge
import InverseGalois.CFT.TateCohomology.RestrictSplit
import InverseGalois.CFT.TateCohomology.RestrictTrans
import InverseGalois.CFT.TateCohomology.Shapiro
import InverseGalois.CFT.TateCohomology.Shift
import InverseGalois.CFT.TateCohomology.ShiftNatural
import InverseGalois.CFT.TateCohomology.ShiftSplit
import InverseGalois.CFT.TateCohomology.Shifting
import InverseGalois.CFT.TateCohomology.SylowInjective
import InverseGalois.CFT.TateCohomology.RestrictOne
import InverseGalois.CFT.TateCohomology.SylowSurjective
import InverseGalois.CFT.TateCohomology.SylowTrivial
import InverseGalois.CFT.TateCohomology.TateClassCount
import InverseGalois.CFT.TateCohomology.TateDegreeTwo
import InverseGalois.CFT.TateCohomology.TateNakayama
import InverseGalois.CFT.TateCohomology.TateNakayamaError
import InverseGalois.CFT.TateCohomology.TateTheorem
import InverseGalois.CFT.TateCohomology.Tensor
import InverseGalois.CFT.TateCohomology.TensorExtension
import InverseGalois.CFT.TateCohomology.TensorFunctor
import InverseGalois.CFT.TateCohomology.TensorPExact
import InverseGalois.CFT.TateCohomology.TensorPTorsion
import InverseGalois.CFT.TateCohomology.TensorPTorsionShift
import InverseGalois.CFT.TateCohomology.TensorPair
import InverseGalois.CFT.TateCohomology.TensorPi
import InverseGalois.CFT.TateCohomology.TensorRight
import InverseGalois.CFT.TateCohomology.TensorShift
import InverseGalois.CFT.TateCohomology.TensorTor
import InverseGalois.CFT.TateCohomology.TensorTorsionError
import InverseGalois.CFT.TateCohomology.TensorTrivial
import InverseGalois.CFT.TateCohomology.TorsionErrorLong
import InverseGalois.CFT.TateCohomology.TorsionFree
import InverseGalois.CFT.TateCohomology.TorsionInduced
import InverseGalois.CFT.TateCohomology.TorsionNakayama
import InverseGalois.CFT.TateCohomology.TorsionShift
import InverseGalois.CFT.TateCohomology.Transfer
import InverseGalois.CFT.TotallyReal
import InverseGalois.CFT.Units.ABHN
import InverseGalois.CFT.Units.ABHNArchimedean
import InverseGalois.CFT.Units.ABHNCoboundary
import InverseGalois.CFT.Units.ABHNFinite
import InverseGalois.CFT.Units.ABHNLocalNorm
import InverseGalois.CFT.Units.ABHNLocalPower
import InverseGalois.CFT.Units.ABHNOnePlace
import InverseGalois.CFT.Units.ABHNPlaces
import InverseGalois.CFT.Units.ABHNRamified
import InverseGalois.CFT.Units.ABHNSqrtNegOne
import InverseGalois.CFT.Units.ABHNSqrtNegOneRamified
import InverseGalois.CFT.Units.ABHNTorsion
import InverseGalois.CFT.Units.ABHNUnitValues
import InverseGalois.CFT.Units.AdicFixed
import InverseGalois.CFT.Units.AdicIdeleHerbrand
import InverseGalois.CFT.Units.AdicLocalNorm
import InverseGalois.CFT.Units.AdicOrbit
import InverseGalois.CFT.Units.AdicOrbitTate
import InverseGalois.CFT.Units.AdicRadical
import InverseGalois.CFT.Units.AdicSIdeles
import InverseGalois.CFT.Units.AdicSOrbitTate
import InverseGalois.CFT.Units.AdicUnitGen
import InverseGalois.CFT.Units.ArchimedeanIdeles
import InverseGalois.CFT.Units.BaseArtin
import InverseGalois.CFT.Units.BaseChangeCocycle
import InverseGalois.CFT.Units.BaseChangeIndex
import InverseGalois.CFT.Units.BaseFundamental
import InverseGalois.CFT.Units.BaseFundamentalCyclic
import InverseGalois.CFT.Units.BaseTate
import InverseGalois.CFT.Units.BaseTateCoeff
import InverseGalois.CFT.Units.BaseTateSylow
import InverseGalois.CFT.Units.BaseTateTorsion
import InverseGalois.CFT.Units.ClassSet
import InverseGalois.CFT.Units.CompletionCyclic
import InverseGalois.CFT.Units.CompletionFinite
import InverseGalois.CFT.Units.CompletionGalois
import InverseGalois.CFT.Units.CompletionHilbert90
import InverseGalois.CFT.Units.CompletionUnits
import InverseGalois.CFT.Units.CompositumEmbed
import InverseGalois.CFT.Units.CompositumFundamental
import InverseGalois.CFT.Units.CyclicTrivial
import InverseGalois.CFT.Units.Decomposition
import InverseGalois.CFT.Units.DecompositionClosed
import InverseGalois.CFT.Units.DecompositionField
import InverseGalois.CFT.Units.DecompositionFieldLevel
import InverseGalois.CFT.Units.DecompositionFieldTower
import InverseGalois.CFT.Units.DecompositionFundamental
import InverseGalois.CFT.Units.DecompositionGalois
import InverseGalois.CFT.Units.DecompositionIdele
import InverseGalois.CFT.Units.DecompositionInvariant
import InverseGalois.CFT.Units.DecompositionLocalization
import InverseGalois.CFT.Units.DecompositionNakayama
import InverseGalois.CFT.Units.DecompositionNakayamaNext
import InverseGalois.CFT.Units.DecompositionOutside
import InverseGalois.CFT.Units.DecompositionPlaceInjective
import InverseGalois.CFT.Units.DecompositionReciprocity
import InverseGalois.CFT.Units.HasseHom
import InverseGalois.CFT.Units.HasseLevel
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.CFT.Units.InfiniteDecompositionField
import InverseGalois.CFT.Units.HasseInflation
import InverseGalois.CFT.Units.HasseDecomposition
import InverseGalois.CFT.Units.HasseTwo
import InverseGalois.CFT.Units.HasseTwoDecomposition
import InverseGalois.CFT.Units.DecompositionRestrict
import InverseGalois.CFT.Units.DecompositionSubgroup
import InverseGalois.CFT.Units.EquivariantLabel
import InverseGalois.CFT.Units.FirstInequality
import InverseGalois.CFT.Units.FrobeniusPlace
import InverseGalois.CFT.Units.GaloisAction
import InverseGalois.CFT.Units.GeneratingPrimes
import InverseGalois.CFT.Units.GlobalFundamental
import InverseGalois.CFT.Units.GlobalTate
import InverseGalois.CFT.Units.GlobalUnitsLocal
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
import InverseGalois.CFT.Units.IdeleClassTorsionLocal
import InverseGalois.CFT.Units.IdeleClassTorsionSES
import InverseGalois.CFT.Units.IdeleClassTorsionSubgroup
import InverseGalois.CFT.Units.IdeleClassTorsionSubgroupLocal
import InverseGalois.CFT.Units.IdeleClassTorsionTate
import InverseGalois.CFT.Units.IdeleClassTower
import InverseGalois.CFT.Units.IdeleCoboundary
import InverseGalois.CFT.Units.IdeleFixed
import InverseGalois.CFT.Units.IdeleFullCompare
import InverseGalois.CFT.Units.IdeleGen
import InverseGalois.CFT.Units.IdeleLocalVanish
import InverseGalois.CFT.Units.IdeleNorm
import InverseGalois.CFT.Units.IdeleNormTower
import InverseGalois.CFT.Units.IdeleOrbitTate
import InverseGalois.CFT.Units.IdeleQuotCyclic
import InverseGalois.CFT.Units.IdeleRep
import InverseGalois.CFT.Units.IdeleRestrict
import InverseGalois.CFT.Units.IdeleTensorOrbit
import InverseGalois.CFT.Units.IdeleTensorSha
import InverseGalois.CFT.Units.IdeleTensorTorsion
import InverseGalois.CFT.Units.IdeleTorsion
import InverseGalois.CFT.Units.IdeleTorsionSubgroup
import InverseGalois.CFT.Units.IdeleTorsionTensor
import InverseGalois.CFT.Units.IdeleTorusSha
import InverseGalois.CFT.Units.IdeleTorusShaLocal
import InverseGalois.CFT.Units.IdeleTorusShaSharp
import InverseGalois.CFT.Units.IdeleTorusShaTorsion
import InverseGalois.CFT.Units.IdeleTower
import InverseGalois.CFT.Units.IdeleValuationSplit
import InverseGalois.CFT.Units.InertPlace
import InverseGalois.CFT.Units.InfiniteComap
import InverseGalois.CFT.Units.InfiniteFixed
import InverseGalois.CFT.Units.InfiniteGalois
import InverseGalois.CFT.Units.InfiniteHilbert90
import InverseGalois.CFT.Units.InfiniteIdele
import InverseGalois.CFT.Units.InfiniteOrbit
import InverseGalois.CFT.Units.InfinitePlaceIdele
import InverseGalois.CFT.Units.InfiniteTowerDescent
import InverseGalois.CFT.Units.InflationDescent
import InverseGalois.CFT.Units.InvariantUniformizer
import InverseGalois.CFT.Units.KummerDecomposition
import InverseGalois.CFT.Units.KummerIdele
import InverseGalois.CFT.Units.KummerShaBot
import InverseGalois.CFT.Units.LocalCoboundaryTwist
import InverseGalois.CFT.Units.LocalDegreeLcm
import InverseGalois.CFT.Units.LocalEmbedding
import InverseGalois.CFT.Units.LocalIdele
import InverseGalois.CFT.Units.LocalNorm
import InverseGalois.CFT.Units.LocalPowIdele
import InverseGalois.CFT.Units.LocalSqrtNegOne
import InverseGalois.CFT.Units.NakayamaSpan
import InverseGalois.CFT.Units.NormIndex
import InverseGalois.CFT.Units.NsmulTorsionRep
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
import InverseGalois.CFT.Units.RadicalDescent
import InverseGalois.CFT.Units.RatFundamentalClass
import InverseGalois.CFT.Units.RatRamIdx
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
import InverseGalois.CFT.Units.StablePlaceIdele
import InverseGalois.CFT.Units.TowerCoboundary
import InverseGalois.CFT.Units.TowerDescent
import InverseGalois.CFT.Units.UnitLattice
import InverseGalois.CFT.Units.UnramifiedSplit
import InverseGalois.CFT.Units.UnramifiedTateRep
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
* `InverseGalois.CFT.BaseCompositum` builds the compositum of a number field with a Galois
  extension of the rationals inside an algebraic closure of the former, without asking the two to
  be given as subfields of a common field.  A primitive element of the smaller factor identifies
  the compositum with the splitting field over the base of the minimal polynomial of that element,
  because normality over the rationals puts every root of that polynomial in the image of the
  chosen embedding; so **the compositum is a finite Galois extension of the base generated by the
  image of the other factor**.  Restriction of automorphisms to that image is injective because an
  automorphism fixing a generating set is the identity, and **surjective as soon as no rational
  prime ramifies in both factors**: the fixed field of the image of restriction has image in the
  compositum fixed by the whole Galois group over the base, hence lands in the base, so no rational
  prime ramifies in it and Minkowski's bound collapses it to the rationals.  Consequently **the
  degree and the cyclicity of the compositum over the base are those of the other factor over the
  rationals** — the shape in which the reciprocity computation over an arbitrary base meets its
  auxiliary cyclic field.
* `InverseGalois.CFT.BaseRamification` transports unramifiedness from the small factor of such a
  compositum to the compositum itself.  **The order of an inertia group is the ramification index**,
  so triviality of inertia is exactly unramifiedness; and **restriction of automorphisms to the
  small factor carries inertia to inertia**, because an automorphism trivial on the residues at a
  place of the compositum is trivial on the residues at the place below.  Since that restriction is
  injective, **a place of the compositum whose trace on the small factor is unramified over the
  rationals is unramified over the number field** — the compositum with a cyclotomic field is
  unramified away from the conductor over an arbitrary base, just as the cyclotomic field is over
  the rationals.
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
* `InverseGalois.CFT.Cyclotomic.SubfieldFrobenius` refines that criterion into a measurement of the
  local degree: the decomposition group of a normal intermediate field is generated by the
  restricted Frobenius, so its order divides a number exactly when that power of the Frobenius
  above it fixes the intermediate field pointwise.
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
* `InverseGalois.CFT.Brauer.CrossedProductInflate` enlarges the splitting field: a cocycle of an
  intermediate extension inflates along the restriction of automorphisms, and the crossed product
  of the inflated cocycle is the algebra of matrices over the original one indexed by a basis of
  the larger field over the intermediate one, so inflation leaves the Brauer class unchanged.
* `InverseGalois.CFT.Brauer.SmoothLevel` descends a smooth two cocycle of the Galois group of an
  arbitrary Galois extension to a finite Galois level: its values lie in the level it is constant
  for, and it is the inflation of a cocycle there.  Inflation is injective on classes, a
  trivialising cochain being correctable to one constant on the cosets of the subgroup fixing the
  level by Hilbert's theorem ninety relative to that level.
* `InverseGalois.CFT.Brauer.InflateTower` assembles the levels into a single homomorphism:
  inflating twice along a tower of normal subfields is inflating once to the top, so two cocycles
  of finite Galois levels with the same smooth class can be compared in their compositum and have
  the same Brauer class.  The resulting map from the smooth second cohomology of the whole Galois
  group to the Brauer group of the base is a homomorphism, and it is injective.
* `InverseGalois.CFT.Brauer.SmoothBrauer` makes it surjective when the top field is an algebraic
  closure of a perfect field: a Brauer class split by a finite Galois extension is the class of a
  crossed product of that extension, so the Brauer group of a perfect field *is* the smooth second
  cohomology of its absolute Galois group with coefficients in the units of an algebraic closure.
* `InverseGalois.CFT.Brauer.SmoothInvariant` composes that with the invariant map: the smooth
  second cohomology of the absolute Galois group of a local field with coefficients in the units
  of an algebraic closure is the rationals modulo the integers.
* `InverseGalois.CFT.Brauer.PlaceInvariant` localizes a Brauer class of a number field at a finite
  place: the completion there is a local field, so base change followed by the local invariant map
  attaches to every class a rational number modulo the integers, and that number vanishes exactly
  when the completion splits the class.  The archimedean members of the family come from a real
  embedding of the base in the same way.  Base change of the smooth second cohomology of an
  absolute Galois group is read off the same identification, and is functorial in the field.
* `InverseGalois.CFT.Brauer.PlaceInvariantFinite` bounds the places at which that number can fail to
  vanish.  A class is the class of a crossed product of a finite Galois extension of number fields,
  only finitely many places ramify, and each of the finitely many values of the cocycle is a unit of
  the valuation ring outside a finite set, so **a Brauer class over a number field is split by the
  completion at all but finitely many finite places**.
* `InverseGalois.CFT.Brauer.InfiniteInvariant` completes the family at the archimedean places.  The
  completion at a complex place is isomorphic over the base to the complex numbers, hence splits
  every class, and the completion at a real place is isomorphic over the base to the reals, hence
  splits exactly the classes split by the associated real embedding, so **every infinite place
  carries an invariant which vanishes exactly when the completion there splits the class**.
* `InverseGalois.CFT.Brauer.PlaceCrossedProduct` computes that localization on crossed products.
  Restricting a cocycle to the decomposition group is base change to the decomposition field, and
  over that field the extension and the completion of the base are linearly disjoint, so a second
  base change reads the cocycle on the Galois group of the completions.  The invariant at the place
  therefore vanishes exactly when the local cocycle is a coboundary.
* `InverseGalois.CFT.Brauer.PlaceCoboundary` reads that criterion on the decomposition group.  The
  two identifications of the decomposition group, with the Galois group of the completions and with
  the Galois group over the decomposition field, agree, so **the invariant at a finite place of the
  class of a crossed product vanishes exactly when the cocycle restricted to the decomposition
  group is a coboundary in the units of the completion** — the shape taken by the local hypotheses
  of the Albert-Brauer-Hasse-Noether theorem.
* `InverseGalois.CFT.Brauer.InfinitePlaceCrossedProduct` runs the same two-step base change at an
  infinite place, where the decomposition field is the subfield fixed by the stabiliser of the
  place: **the completion at an infinite place splits the class of a crossed product exactly when
  the cocycle restricted to the decomposition group is a coboundary in the units of the
  completion.**
* `InverseGalois.CFT.Brauer.LocalSymbol` feeds the `n`-th power symbol through that
  identification.  An algebraic closure is closed under `n`-th roots, so nothing is lost in reading
  the symbol of two units in the units of the closure, and the invariant map turns it into a
  rational number modulo the integers killed by `n`: **the norm residue symbol of a local field**,
  bimultiplicative and trivial as soon as one of its arguments is an `n`-th power.
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
* `InverseGalois.CFT.Tate.FamilyCoind` removes the choice from that comparison and extends it to a
  group that need not be cyclic.  A section of a family over a transitively acted upon index set is
  remembered by the function on the group sending an element to the value, at a base point, of the
  translated section; that function is equivariant for the stabiliser of the base point, every
  equivariant function arises from exactly one section, and translating a section translates the
  function, so **the sections of a family over a transitive orbit are the representation coinduced
  from the module at the base point**.  Coinduction is transparent to complete cohomology, so **the
  complete cohomology of the sections is the complete cohomology of the stabiliser of the base point
  with coefficients in the module there**: for the local factors of the group of ideles at the
  places above a place of the base field, the stabiliser is the decomposition group and the module
  is the local factor at one place above it.
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
* `InverseGalois.CFT.Tate.FamilyRestrictCoind` reads the same restriction through coinduction
  instead of through the Herbrand quotient, and so needs no hypothesis on the group beyond
  finiteness.  The sections of a family over a transitive orbit are coinduced from the module at a
  base point, so the contribution of an orbit to a restriction is the complete cohomology of the
  stabiliser of that point with coefficients in the subgroup there; identifying that subgroup with
  whatever group it is declared to be carries the computation along, and an orbit whose declared
  action has no complete cohomology contributes nothing in that degree.
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
* `InverseGalois.CFT.Tate.FamilyProduct` does the same for an arbitrary finite group and in every
  degree at once.  Reindexing along the decomposition of the index set into its orbits and splitting
  a disjoint union are both isomorphisms of representations, so **the sections of a family are the
  product over the orbits of the sections over one orbit**; the complete cohomology of a product is
  the product of the complete cohomologies, and the sections over one orbit are coinduced from the
  stabiliser of a chosen point.  Chaining the three gives **the complete cohomology of the sections
  as a product of local contributions, one for each orbit, each computed in the stabiliser of a
  point of that orbit** — for the ideles of a Galois extension of number fields, a product over the
  places of the base field of cohomology groups of decomposition groups — and in particular the
  sections have no cohomology in a degree as soon as no local contribution has any.
* `InverseGalois.CFT.Tate.FamilyTorsion` applies that decomposition to the elements killed by a
  fixed integer.  Those form a subgroup of every abelian group and are carried onto one another by
  every isomorphism, so a family of modules has a subfamily of them, and the sections of the
  subfamily are exactly the sections of the family killed by the integer.  The conclusion is **the
  complete cohomology of the sections killed by an integer as a product over the orbits of the
  index set of the complete cohomology of a stabiliser with coefficients in the elements killed by
  that integer there**.  For the ideles of a Galois extension of number fields the sections killed
  by a prime are the `p`-torsion of the idele group, the orbits are the places of the base field
  and the local coefficients are the roots of unity of the completions.
* `InverseGalois.CFT.Tate.TorsionRep` supplies the two elementary manipulations that stand between
  that decomposition and a module of arithmetic origin.  A subgroup containing every element of the
  ambient module killed by an integer has exactly those elements as its own, so passing to the
  subgroup changes nothing; and the elements of a product of two modules killed by an integer are
  the pairs of elements killed by it, so a module visibly built from two halves contributes the
  product of the two answers.  Both are recorded as isomorphisms of representations, so complete
  cohomology is carried along them, as it is along an equality of actions on a fixed module.
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
* `InverseGalois.CFT.Tate.FamilyCoboundaryOne` is the same passage in degree one, where it is both
  shorter and sharper.  A one-cocycle with values in the sections of a family whose restriction to
  the stabiliser of every index is a coboundary there is **a coboundary**, and the trivialising
  section is written down: at each index it is the local trivialising element at the orbit
  representative, transported forward by a group element carrying the representative to the index
  and corrected by the value of the cocycle at that group element.  Independence of the choice of
  that group element is exactly the local identity at the representative, so no transversal and no
  finiteness of any kind is needed.
* `InverseGalois.CFT.Tate.FamilyH1Local` reads that as a statement about cohomology classes.
  Evaluation at an index is a map of representations of any subgroup fixing the index, so a class
  in the first cohomology of the sections has a local class at every index: restrict to the
  stabiliser, then evaluate.  **A class all of whose local classes vanish is zero.**  This is
  Shapiro's lemma in the only form the ideles need, and it costs nothing beyond the coboundary
  theorem: the local hypothesis is consumed at the level of cochains, so no naturality statement
  for a comparison of coinduced modules ever has to be proved.
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
* `InverseGalois.CFT.Kummer.InfiniteLevelPower` frees that criterion from the extension being
  finite.  A radical of an arbitrary Galois extension generates a finite Galois subextension, and
  the place of that subextension below the given prime carries a decomposition group onto which the
  decomposition subgroup above maps; so an automorphism of the subextension fixing the place is the
  restriction of one fixing the prime, and therefore fixes the radical.  The place of the base below
  the place of the subextension is the place of the base below the given one, so the completion in
  which the root is found is the intended one, at a prime of the integers and at an archimedean
  place alike.
* `InverseGalois.CFT.Kummer.DecompositionLocalPower` turns that criterion into the comparison of the
  two readings of a local condition on a cohomology class.  The profinite reading says that a unit
  of a level becomes a `p`-th power in the compositum of the level with the fixed field of a
  decomposition subgroup; the idelic one says that it becomes a `p`-th power in the completion at
  the place below.  An automorphism over the level lying in the subgroup fixes both factors of the
  compositum, hence a `p`-th root there, so the criterion applies and the first reading implies the
  second.  A class is not a unit but an element of a tensor product of the units with coefficients
  of finite rank over the field with `p` elements, where divisibility by `p` is read coordinate by
  coordinate along a basis of the coefficients; so the comparison for a single unit carries the
  whole class from the compositum to the completion, at a prime and at an archimedean place alike.
* `InverseGalois.CFT.Kummer.LocalPowRepresentatives` makes the local power classes finite and
  represents them globally.  The `n`-th powers have finite index in the units of a completion of a
  number field, the index being the product of the absolute value of `n` there with the number of
  `n`-th roots of unity; weak approximation prescribes a single element of the field at one place up
  to an `n`-th power, so the units of the field surject onto that finite group and a section of the
  surjection has finite range.  Finitely many units of the field therefore meet every power class of
  the completion, at a prime and at an archimedean place alike.
* `InverseGalois.CFT.Kummer.LocalPowerRange` states the criterion for a radical in the form an
  infinite extension needs.  An element fixed by the decomposition group at a place has an image in
  the completion coming from the completion below, that completion being the fixed field of the
  decomposition group acting on the one above; conversely an element whose image has the same `n`-th
  power as an element of the completion below is fixed there, the two differing by a root of unity
  already present in the base.  The radicand is not asked to lie in the base, only the local root,
  which is what lets a Kummer argument run for an element of a compositum.
* `InverseGalois.CFT.Kummer.SupKummerData` carries a Kummer situation up to a larger level.  A
  primitive root of unity of the smaller level stays primitive in the larger one, so every root of
  unity there is one of its powers and already comes from below; the injectivity of the parameter
  group and the vanishing of its `p`-th powers travel along the inclusion of the units, and the
  roots of the units of the larger level are supplied by the ambient extension.  Nothing is asked
  of the action of the Galois group of the larger level, a Kummer situation forcing it to be
  trivial, so the trivial action is the one that is taken.
* `InverseGalois.CFT.Kummer.SupPowSurjective` shows the compositum is no larger than the level
  modulo `p`-th powers.  A `p`-th root of a given unit of the compositum, together with `p`-th roots
  of the finitely many representatives of the local power classes, generates a single finite Galois
  level; there the unit is fixed by the decomposition group, so its image in the completion comes
  from below and is a representative times a `p`-th power, and the corresponding quotient of roots
  is a radical whose local `p`-th power comes from below, hence lies in the compositum.  Choosing
  the representatives before the level is what keeps the argument inside one finite extension.
  Tensoring with coefficients of finite rank over the field with `p` elements preserves the
  conclusion, a `p`-th power crossing the tensor sign to annihilate the coefficients, so the units
  of the level surject onto the units of the compositum with the coefficients attached.
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
* `InverseGalois.CFT.Units.AdicOrbitTate` reads the same family through coinduction instead of
  through the Herbrand quotient, and so loses the hypothesis that the Galois group be cyclic.  The
  places above a fixed finite place of the base field are one orbit, so the units of the completions
  at them are the representation coinduced from the units of the completion at any one of them, and
  **the complete cohomology of the local factor of the ideles at a finite place of the base field is
  the complete cohomology of the decomposition group with coefficients in the units of the
  completion at a place above it**, in every integer degree.  The same argument at an infinite
  place, which differs from the finite one only in the family it is applied to, gives the same
  description of the local factor there.
* `InverseGalois.CFT.Units.UnramifiedTateRep` computes one of those local coefficients outright.
  At an unramified place the decomposition group is generated by a single element and the base
  field already contains a uniformizer, so both middle degrees of the complete cohomology of the
  units of the valuation ring vanish — the lower one by Hilbert's theorem 90 with the uniformizer
  absorbing the valuation of the representative, the upper one because the Herbrand quotient is
  one.  Periodicity for a group with one generator then propagates the vanishing in both
  directions: **the units of the valuation ring of the completion at an unramified finite place
  have no complete cohomology in any degree at all.**  The places outside a finite set therefore
  contribute nothing, which is what lets the ideles be replaced by the ideles that are units
  outside that set.
* `InverseGalois.CFT.Units.IdeleOrbitTate` puts the local factors back together.  The places of the
  extension are the disjoint union of the orbits, one for each place of the base field, so the
  units of all the completions are the product of the local factors and complete cohomology turns
  that product into a product: **in every degree the complete cohomology of the group of ideles is
  the product, over the places of the base field, of the complete cohomology of the decomposition
  group of a place above it with coefficients in the units of the completion there** — for the
  finite places and for the infinite ones alike, with no hypothesis on the Galois group beyond
  finiteness.  In particular the ideles have no cohomology in a degree in which no local factor
  has any.
* `InverseGalois.CFT.Units.IdeleTensorOrbit` carries that description across a twist of the
  coefficients.  Coefficients of finite rank over a prime field are finitely presented, so tensoring
  with them commutes with the product over the places and with coinduction from a decomposition
  group, and the two operations may be performed in either order.  Hence **in every degree the
  complete cohomology of the group of ideles tensored with such coefficients is the product, over
  the places of the base field, of the complete cohomology of the decomposition group of a place
  above it with coefficients in the units of the completion there tensored with the restricted
  coefficients** — again for the finite places and for the infinite ones alike.
* `InverseGalois.CFT.Tate.FamilyConst` singles out the family with a single group repeated at every
  index, all of its transports being the identity.  Its sections are the functions from the index
  set to that group, and **the action assembled from the transports is the permutation action**: a
  group element moves a function by moving its argument backwards.  That is the family measuring
  the valuations of an idele — the valuation at a finite place of a number field is an integer
  whatever the place is, and an automorphism carries the valuation at a place to the valuation at
  the image place — and the reading is completed by the observation that **scaling an invariant
  section by a vector of integers is equivariant for the permutation action on the vector**, which
  is what makes a right inverse of the vector of valuations a map of representations.
* `InverseGalois.CFT.Units.IdeleTorsion` reads the elements of the ideles killed by a nonzero
  integer place by place.  Such an element has every local component killed by that integer, so its
  local valuation, an integer killed by a nonzero integer, vanishes at every finite place; the
  finiteness condition that cuts the ideles out of the product of all the local unit groups is
  therefore automatic, and those elements are exactly the elements of the whole product killed by
  the integer — a root of unity at every place, with no restriction at all.  Splitting that product
  into the infinite half and the finite half and applying the orbit decomposition to each gives
  **the complete cohomology of the elements of the ideles killed by a nonzero integer as the
  product, over the places of the base field, of the complete cohomology of the decomposition group
  of a place above it with coefficients in the elements killed by that integer of the units of the
  completion there**, and in particular the vanishing of the whole as soon as every local factor
  vanishes.
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
* `InverseGalois.CFT.Units.AdicSOrbitTate` reads that restriction in every degree at once.  Above a
  place of the set the local subgroup is everything, so the contribution is the complete cohomology
  of the decomposition group with coefficients in the units of the completion, exactly as for the
  whole group of ideles; above an unramified place outside the set the local subgroup is the units
  of the valuation ring of an unramified extension, whose complete cohomology vanishes in every
  degree.  So **the ideles that are units outside a set of places have no complete cohomology in a
  degree as soon as no local factor at a place of the set has any**, provided every place outside
  the set is unramified.
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
* `InverseGalois.CFT.Units.RatRamIdx` computes that ramification index over the rationals.  The ring
  of integers of the rationals is the rational integers, so the structure map from the rational
  integers is surjective and the ideal below a place extends to the same ideal whichever of the two
  is used as the base; since the ramification index depends on the base only through the extended
  ideal, it agrees with the ramification index over the rational integers, and is therefore one
  whenever the place is unramified in the sense of commutative algebra.  For a place of a subfield
  of the cyclotomic field of conductor `n` lying over a rational prime not dividing `n` this is the
  cyclotomic unramifiedness already available.
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
* `InverseGalois.CFT.Units.DecompositionGalois` packages that as an isomorphism of groups: the
  decomposition group at a prime **is** the Galois group of the completion over the completion of
  the prime below, so its order is the local degree.
* `InverseGalois.CFT.Units.DecompositionInvariant` reads a class of the decomposition group with
  coefficients in the units of the completion as a rational modulo the integers.  The two groups
  acting on those units — the decomposition group and the Galois group of the completions — are
  identified by that isomorphism, and the identification matches their actions, so transporting
  cohomology along it makes the complete cohomology in degree two of the decomposition group the
  second cohomology of a finite Galois extension of local fields.  The crossed product construction
  turns the latter into the Brauer classes of the completion of the base split by the completion of
  the extension, and the invariant map of a local field reads such a class as a rational modulo the
  integers, killed by the local degree.  Since the invariant map of a local field is injective,
  **a class of the decomposition group at a finite place is determined by its invariant.**
* `InverseGalois.CFT.Units.DecompositionFundamental` pins down the class the local theory is about.
  The crossed product construction is an isomorphism onto the relative Brauer group of the
  completions, and local reciprocity counts that group: it has as many elements as the local
  degree.  So **the complete cohomology in degree two of a decomposition group at a finite place
  has as many elements as the local degree**, and, the invariant being injective and killed by the
  degree, **every rational modulo the integers killed by the local degree is the invariant of
  exactly one class.**  The reciprocal of the local degree has the local degree as its order, so
  the class it names — **the fundamental class of the decomposition group** — has that order too,
  which is the number of elements of the whole group: **the complete cohomology in degree two of a
  decomposition group at a finite place is cyclic, generated by its fundamental class.**
* `InverseGalois.CFT.Units.DecompositionSubgroup` spreads that description over every subgroup at
  once.  A subgroup of the decomposition group is again the automorphism group of the completion,
  this time over the subfield it fixes, and that subfield is an intermediate field of a finite
  extension of a local field, hence a local field itself.  So Hilbert's theorem 90 gives **the
  vanishing of the complete cohomology of the units of the completion in degree one on every
  subgroup**, and local reciprocity over the fixed subfield, read through the crossed product
  construction, gives **exactly as many classes in degree two as the subgroup has elements**.  The
  order of the decomposition group is the local degree, which is the order of the fundamental
  class, so the classical hypotheses of Tate's theorem hold on every subgroup: **the units of the
  completion at a finite place are the module of a class formation for the decomposition group**,
  and the theorems of Tate and of Tate and Nakayama apply to them.
* `InverseGalois.CFT.Units.DecompositionReciprocity` matches the two invariants the theory carries
  at a finite place.  One is attached to a Brauer class of the base and reads it after extending
  scalars to the completion; the other is attached to a class of the decomposition group and reads
  it after turning that class into a Brauer class of the completion.  A two-cocycle of the whole
  Galois group has a localization at each place, and the crossed product of the localization is the
  crossed product of the cocycle extended to the completion, so **the invariant at a place of the
  class of a global crossed product is the invariant of the class of the decomposition group at any
  place above it.**  The product formula for the invariants of a Brauer class therefore reads as a
  statement about decomposition groups, and it says something no local argument can: if the
  localizations of a global cocycle are coboundaries at every finite place but one, and the class is
  split at every infinite place, the invariant left over is the inverse of a product of trivial ones
  and so is trivial too.  All the local invariants then vanish, and the theorem of Albert, Brauer,
  Hasse and Noether applies: **one place may be left out of a local-global hypothesis for free.**
* `InverseGalois.CFT.Units.DecompositionIdele` puts the units of a completion inside the ideles.
  An idele supported at a single finite place is carried by an automorphism to an idele supported
  at the image place, so the ideles supported at one place are stable exactly under the
  automorphisms fixing it, and on that subgroup the embedding is equivariant: the automorphism
  moves the components of an idele around and moves the units of the completion by the action of
  the decomposition group, and the two agree because the transport of the family at a place left
  where it is **is** that action.  So **the units of the completion at a finite place are a
  subrepresentation of the ideles for the decomposition group there**, and composing with the
  passage to classes lands them in the idele class group.  Reading the component at the place is
  equivariant for the same reason, and it recovers the unit an idele supported there was built
  from, so **the units of the completion are a retract of the ideles for the decomposition group**
  and the embedding stays injective after any functor is applied to it.
* `InverseGalois.CFT.Units.InfinitePlaceIdele` reads the archimedean components of an idele.  An
  automorphism permutes them exactly as it permutes the finite ones, so reading the component at an
  infinite place is equivariant for the decomposition group there; the component of a principal
  idele is the image of the unit in the completion, and the component of an idele supported at a
  finite place is trivial.  These are the archimedean halves of the computations that separate one
  finite place from all the others.
* `InverseGalois.CFT.Units.StablePlaceIdele` treats a finite place fixed by the whole Galois group,
  where the group is its own decomposition group.  A two-cocycle with values in the units of the
  completion there whose ideles bound in the idele class group already bounds upstairs: a bounding
  one-cochain of the classes lifts to the ideles, the failure of the lift to bound is a two-cocycle
  of the units of the top field which at every place other than the distinguished one is the
  coboundary of the component of the lift, and one place left out is exactly what the product
  formula pays for.  Correcting the lift by the resulting global one-cochain bounds the cocycle on
  the nose, so **the second cohomology of the units of the completion at a finite place fixed by
  the whole Galois group injects into the second cohomology of the idele class group.**
* `InverseGalois.CFT.Units.DecompositionPlaceInjective` removes the hypothesis on the place.  The
  decomposition group at a finite place is the Galois group of the extension over the decomposition
  field, and over that field the place is fixed by the whole group, so the statement transports by
  nothing more than renaming the group: **a two-cocycle of the decomposition group at a finite place
  with values in the units of the completion there whose ideles bound in the idele classes is a
  coboundary.**  Counting turns the resulting injection into a bijection — the source has exactly as
  many elements as the group by local reciprocity, the target at most that many by the second
  inequality — so **the second cohomology of the units of a completion at a finite place is the
  second cohomology of the idele class group on the decomposition group there**, and the order of
  the latter is pinned to the local degree.
* `InverseGalois.CFT.Units.DecompositionLocalization` inverts that isomorphism.  A class of the
  idele class group, restricted to a decomposition group, becomes a class of the units of the
  completion: the localisation of a global class at a place.  Applied to the fundamental class of
  the extension it produces at every finite place a class whose ideles are, by construction, the
  restriction of the fundamental class, and which is a fundamental class in its own right — only
  the multiples of the order of the decomposition group annihilate it, so it generates, its order
  is the degree of the extension of the completions, and its invariant is a rational with exactly
  that denominator.  **The classical hypotheses of Tate's theorem hold for it on every subgroup of
  the decomposition group**, so it serves everywhere the local fundamental class serves, while its
  relation to the global class is an equation and not a comparison of invariants.
* `InverseGalois.CFT.Units.DecompositionNakayama` reads the comparison of Tate and Nakayama at a
  decomposition group.  The comparison attached to the idele class group and the fundamental class,
  read there, is the comparison of that group for the restricted class, and the localised
  fundamental class is a class of the units of the completion whose ideles are that restriction.
  So **everything the comparison produces on a decomposition group already comes from the units of
  the completion at the place**, and a fortiori from the ideles: on a decomposition group the
  classes of the idele classes the comparison reaches are classes of ideles, with no information
  about the extension away from the place.
* `InverseGalois.CFT.Units.DecompositionNakayamaNext` does the same for the map that leaves the
  comparison.  The localised fundamental class is carried to the restriction of the fundamental
  class, so the two extensions attached to those classes are compared by a map of representations,
  and **on the decomposition group at a finite place the values the map leaving the comparison
  takes on the classes coming from the units of the completion there are exactly the image of the
  values the purely local map takes**.  Again nothing about the extension away from the place
  enters, so the local half of the comparison of the global obstruction with the local ones is a
  computation at one place.
* `InverseGalois.CFT.Units.DecompositionField` names the subfield fixed by the decomposition
  group.  An element of it has its image in the completion fixed by the decomposition group, hence
  coming from the completion of the base, so the decomposition field embeds into the completion of
  the base and the Galois group of the completions is the Galois group over it.
* `InverseGalois.CFT.Units.DecompositionFieldTower` moves that description along a tower.  An
  element of the top field lies in the decomposition field of a level exactly when its image in the
  completion above comes from the completion of the level, and an automorphism of the top field
  fixing the prime restricts to one of the level fixing the prime below; the transport of the
  completions along the tower carries the completion of the level to itself, so the decomposition
  field of the level is stable under every automorphism fixing the prime and its embedding into the
  completion of the level intertwines the two actions.
* `InverseGalois.CFT.Units.DecompositionFieldLevel` reads the decomposition field of a level from
  the big extension above it.  A finite Galois level contains any given level together with any
  given finite set of elements, so the levels are cofinal; and **an element of a level lies in the
  decomposition field of the level over a smaller level exactly when every automorphism of the whole
  extension fixing the prime and the smaller level pointwise fixes it** — one direction restricts
  such an automorphism to the level, the other lifts an automorphism of the level fixing the prime
  below and observes that the lift fixes the smaller level because its restriction does.
  Restricting an automorphism fixing the prime first to the level and then to the smaller one is
  restricting it to the smaller one directly, so the embedding of the decomposition field into the
  completion of the smaller level is equivariant for the automorphisms fixing the prime.
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
* `InverseGalois.CFT.Units.InfiniteDecompositionField` names the subfield fixed by the stabiliser
  of an infinite place.  An element of it has its image in the completion fixed by that stabiliser,
  hence coming from the completion of the base, so the decomposition field embeds into the
  completion of the base and the automorphism group of the completions is the Galois group over it.
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
* `InverseGalois.CFT.Units.InertPlace` reads the same generation statement as a statement about the
  supply of places.  No proper subgroup of a solvable Galois group contains every decomposition
  group away from a finite set of places of the base, so for a cyclic extension an exponent which
  does not kill a generator fails to kill some element of some such decomposition group, the
  elements killed by a fixed exponent forming a subgroup.  When the degree is a power of a prime the
  orders of the elements are powers of that prime, hence totally ordered by divisibility, so an
  element escaping the largest proper exponent has the order of a generator and therefore generates:
  **a cyclic extension of prime power degree has a finite place, away from any prescribed finite set
  of places of the base, whose decomposition group is the whole Galois group**, and discarding the
  finitely many ramified places as well makes the arithmetic Frobenius there a generator of the
  Galois group, with no analysis at all.
* `InverseGalois.CFT.Units.LocalDegreeLcm` collects those places prime by prime.  For every prime
  dividing the degree of a cyclic extension, the exponent obtained by dividing the degree by that
  prime does not kill a generator, so some place away from a prescribed finite set of places of the
  base has local degree not dividing it; and a divisor of the degree which is not the whole degree
  divides the degree divided by some prime factor.  Hence **finitely many places, all lying over
  primes outside the prescribed set, have local degrees whose least common multiple is the degree**,
  or equivalently the degree and the complementary degrees at those places have greatest common
  divisor one.  This is the arithmetic input for the surjectivity of the sum of the local
  invariants: each prime part of the degree is already carried by a single place.
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
* `InverseGalois.CFT.Units.DecompositionClosed` puts a decomposition subgroup of an infinite
  extension into the Galois correspondence.  An automorphism fixes a prime of the integers exactly
  when it respects the membership of every integer, and it fixes an archimedean place exactly when
  it preserves the absolute value of every element; each of those conditions cuts out the preimage
  of a set in a discrete space under a continuous map, so **every decomposition subgroup is closed**
  and hence **is the subgroup fixing its own fixed field.**
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
  second cohomology as soon as a normal subgroup and the quotient do.  Only the third of the three
  corrections reads anything about the first cohomology of the subgroup, and it reads only the
  family of one-cocycles `x ↦ a (σ, σ⁻¹ x σ)` indexed by the elements `σ` of the group; so the same
  file proves the sharper statement that **a two-cocycle restricting to a coboundary on a normal
  subgroup and whose transgression is a coboundary as a family is cohomologous to an inflated
  cocycle**, with the vanishing of the whole first cohomology as the case of a trivial family.
* `InverseGalois.CFT.GroupCohomology.Transgression` identifies that family when the subgroup acts
  trivially on the module, which is the situation of an embedding problem split by the fixed field
  of the subgroup.  Triviality of the action makes each `x ↦ a (σ, σ⁻¹ x σ)` a homomorphism on the
  subgroup, invariant under conjugation by it, so depending only on the coset of `σ`, and the
  cocycle identity in two variables becomes the one-cocycle identity in one: **the transgression is
  a one-cocycle of the quotient with values in the homomorphisms from the subgroup to the module**.
  The obstruction to a class being inflated is therefore a class of the quotient, a finite object
  even when the subgroup is enormous, and the criterion for inflation is that it be a coboundary.
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
* `InverseGalois.CFT.Units.IdeleClassTorsionSES` restricts that sequence to the elements killed by a
  fixed integer.  Injectivity of the first map and exactness in the middle survive the restriction
  untouched, since both are read off from the same equations; what needs an argument is that the
  second map stays surjective, because a class killed by the integer is only represented by an idele
  whose power is a principal idele.  That principal idele comes from a unit of the field which is a
  power in every completion, so for a prime exponent Wang's theorem makes it a power in the field,
  and subtracting the principal idele of a root moves the representative to one killed by the
  exponent without changing its class.  **For a prime exponent the elements killed by that prime of
  the units, of the ideles and of the idele classes again form a short exact sequence of
  representations of the Galois group.**
* `InverseGalois.CFT.Units.IdeleClassTorsionTate` reads its long exact sequence.  Two of the three
  terms are known: the middle one is, in every degree, the product over the places of the base field
  of the complete cohomology of a decomposition group with coefficients in the roots of unity of a
  completion, and the term on the left is the complete cohomology of the roots of unity of the field
  itself.  Read forwards this gives a vanishing criterion — **the idele classes killed by the prime
  have no complete cohomology in a degree in which no local factor has any and the roots of unity of
  the field have none one degree higher.**  Read backwards it identifies the image of the connecting
  map: **the everywhere locally trivial classes of the roots of unity of the field are exactly the
  classes coming from the idele classes killed by the prime, one degree lower.**
* `InverseGalois.CFT.Units.IdeleClassTorsionLocal` runs the same long exact sequence after tensoring
  with coefficients, which is where it is needed, the idele classes killed by a prime tensored with
  coefficients being exactly what measures the failure of the theorem of Tate and Nakayama for
  coefficients with torsion.  The sequence stays exact because its middle term is killed by the
  prime, and the middle group of the three is again a product of local ones once the coefficients
  have finite rank over the prime field.  So **a class of the idele classes killed by a prime,
  tensored with the coefficients, is the image of a family of local classes exactly when the
  connecting map kills it**, one member of the family for each place of the base field; and every
  class is of that form as soon as the roots of unity of the field, tensored with the coefficients,
  carry no complete cohomology one degree higher.
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
* `InverseGalois.CFT.Units.UnramifiedSplit` extracts from that same uniformizer the splitting a
  twist needs.  Subtracting from a unit of the completion the power of a fixed uniformizer carrying
  its valuation is a homomorphism onto the units of the valuation ring which commutes with the
  action and is the identity on those units, so **the units of the valuation ring at an unramified
  place are a retract of the whole local factor**.  Tensored coefficients destroy the vanishing of
  the complete cohomology of the units of the valuation ring but not the retraction, and **the
  complete cohomology of those units with twisted coefficients therefore injects into that of the
  local factor.**
* `InverseGalois.CFT.Units.IdeleCoboundary` globalises that: a two-cocycle with values in the ideles
  which is a coboundary at every place is a coboundary.  The coordinates in a Galois orbit determine
  one another, so a local one-cochain at each place assembles into a global one; at all but the
  finitely many places which are ramified or where the cocycle is not a unit, the local cochain may
  be chosen with values in the units of the valuation ring, and the assembled family is an idele.
* `InverseGalois.CFT.GroupCohomology.MapCoboundary` records the elementary fact that a map of
  representations which is injective on second cohomology reflects coboundaries, which is how an
  injectivity statement coming from a long exact sequence gets applied to an explicit cocycle.
* `InverseGalois.CFT.GroupCohomology.MapInjective` records the converse packaging.  A class in
  second cohomology is the class of a two-cocycle and vanishes exactly when that cocycle is a
  coboundary, so **a map of representations which reflects coboundaries in degree two is injective
  on second cohomology** — the shape in which an injectivity statement is produced by an explicit
  computation with cochains rather than consumed by one.
* `InverseGalois.CFT.Units.ABHN` combines the two halves.  The second cohomology of the units
  injects into the second cohomology of the ideles, and a two-cocycle of the ideles which is locally
  a coboundary is a coboundary, so **a two-cocycle with values in the units of the top field which
  is a coboundary at every place is a coboundary** — the Albert-Brauer-Hasse-Noether theorem in the
  shape of the vanishing of the second Tate-Shafarevich group of the units.
* `InverseGalois.CFT.Units.ABHNOnePlace` spends the product formula on that statement.  The local
  invariants of a Brauer class multiply to one, so the invariant at any single place is determined
  by all the others and one place costs nothing to leave out: **a two-cocycle of the Galois group
  with values in the units of the top field which is a coboundary at every infinite place and at
  every finite place but one is a coboundary.**  The hypotheses are stated on explicit cochains,
  which is the form in which a cocycle arrives from a long exact sequence.
* `InverseGalois.CFT.Brauer.HasseNoether` reads that on the Brauer group.  Every class over a
  number field is split by a finite Galois extension and is therefore the class of a crossed
  product of it, base change to a completion is base change of the cocycle to the decomposition
  group, and a cocycle which is a coboundary at every place is a coboundary; so **a Brauer class
  over a number field which is split by every completion is trivial**, and **the Brauer group of a
  number field injects into the product of the Brauer groups of its completions.**
* `InverseGalois.CFT.Brauer.TotalInvariant` collects the local invariants into a single family, one
  rational number modulo the integers for each place.  All but finitely many of them vanish, so
  their sum over all places is defined, and a class with all of them zero is split everywhere:
  **a Brauer class over a number field is determined by its family of local invariants.**
* `InverseGalois.CFT.Brauer.TotallyRealInvariant` removes the archimedean places from that sum for
  the classes the reciprocity computation is about.  Every infinite place of the rationals is real,
  so the completion there splits exactly what the reals split, and a field with a real embedding
  therefore splits at every infinite place whatever it splits globally.  A totally real number
  field supplies such an embedding from any of its own infinite places, so **the total invariant of
  a cyclic algebra over the rationals with a totally real splitting field is the product of its
  invariants at the finite places.**
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
* `InverseGalois.CFT.Units.ABHNUnitValues` removes the torsion hypothesis from that observation.  A
  unit of a number field has nonzero order at only finitely many primes, so each value of a
  two-cocycle of the units is a unit of the valuation ring at all but finitely many places, and
  **at an unramified place where every value of the cocycle is such a unit the local component is a
  coboundary**.
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
* `InverseGalois.CFT.GroupCohomology.AbelianLift` runs the same engine with the centrality dropped.
  For a merely abelian kernel the factor set is still a two-cocycle, now for the action of the
  quotient by conjugation through the section, and correcting the section by a trivialising cochain
  still produces a homomorphic lift; the kernel is presented as an abstract abelian group with an
  injection into the source, so **a caller may supply the module structure it already has** rather
  than transport one onto a subtype.  The converse also holds: the factor set pulled back along a
  homomorphism which lifts is the coboundary of the difference between the section and the lift.
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
* `InverseGalois.CFT.TateCohomology.GroupCongr` transports cohomology along an isomorphism of
  groups.  A homomorphism of groups together with a compatible map of coefficients composes a
  cochain with the homomorphism in its arguments and with the coefficient map in its values; when
  the homomorphism is an isomorphism and the coefficient map is bijective, both operations are
  bijections, so the induced map of complexes of inhomogeneous cochains is an isomorphism in every
  degree and hence an isomorphism of complexes.  Homology carries that to an isomorphism, so **the
  cohomology of a group with coefficients in a representation depends on the pair only up to
  isomorphism**, which is what lets a computation made for one presentation of a group be read off
  for another.
* `InverseGalois.CFT.TateCohomology.DeltaNatural` compares the long exact sequences of two short
  exact sequences joined by a map: **the connecting map of the complete cohomology commutes with a
  map of short exact sequences in every integer degree.**  Away from the two middle degrees this is
  the naturality of the connecting map of a map of complexes; out of degree zero and into degree
  minus one it follows from that same naturality once the comparison of the ordinary cohomology and
  homology in degree zero with the invariants and the coinvariants is known to be natural.  Out of
  degree minus one there is no ordinary connecting map behind it: a class there is computed from a
  vector of the middle whose norm comes from the sub, the map of sequences carries such a vector to
  another one, and both ends of the snake are carried along with it.
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
* `InverseGalois.CFT.TateCohomology.ShiftNatural` makes those two identifications natural.  A map of
  representations induces a map of the functions on the group, by composing a function with it; that
  map carries the record of the translates of a vector to the record of the translates of its image,
  so it descends to the shifts, and it commutes with the summation, so it restricts to the coshifts.
  Both defining sequences are therefore functorial with the functions on the group in the middle,
  and since the connecting map of the complete cohomology commutes with a map of short exact
  sequences, **both moves of the degree commute with a map of representations**.  A dimension
  shifting argument can then be carried along a diagram instead of being applied to one
  representation at a time.
* `InverseGalois.CFT.TateCohomology.ShiftSplit` observes that the two defining sequences are split
  once the action is forgotten.  A vector placed at the unit of the group sums to that vector, so it
  is a section of the summation, and subtracting the vector so placed at the unit retracts the
  functions on the group onto the kernel of the summation; the value at the unit of the group
  recovers a vector from the record of all of its translates, and subtracting the record of the
  translates of that value kills the translates and so descends to a section of the passage to the
  shift.  Neither splitting is equivariant, and neither can be, since an equivariant one would make
  the complete cohomology of the representation a summand of a group that vanishes.  What they give
  is **the hypothesis under which an extension compares with the two defining sequences**, and the
  two defining sequences satisfy it themselves.
* `InverseGalois.CFT.TateCohomology.Cyclic` compares the shift with the coshift directly, for a
  group generated by a single element.  Send a function on the group to the function whose value at
  a point is the value of the original at the point translated by the generator, corrected by the
  inverse action of the generator, minus the original value.  This twisted difference is
  equivariant, because every element of the group commutes with the generator; it kills exactly the
  record of the translates of a vector, because a function killed by it is determined by its value
  at the neutral element; and its values are exactly the functions whose values sum to zero,
  because a telescoping sum inverts the difference against the generator whenever the total
  vanishes.  So it identifies the shift with the coshift, the two moves of the degree compose, and
  **the complete cohomology of a representation of a finite cyclic group in a degree is its
  complete cohomology two degrees lower**.  A vanishing statement in one degree therefore
  propagates to every second degree above it, which is what makes the arithmetic of a cyclic
  extension computable.
* `InverseGalois.CFT.TateCohomology.CyclicVanishing` turns that periodicity into a criterion an
  arithmetic input can meet.  The two middle degrees are elementary — degree zero is the invariants
  modulo the norms and degree minus one is the classes in the coinvariants killed by the norm — so
  asking them to vanish is asking that every invariant vector be a norm and that every vector killed
  by the norm be the difference of a vector and one of its translates, which is exactly the shape a
  computation in a cyclic extension produces.  For a group generated by a single element the norm is
  moreover the plain sum of the powers of that element below its order, so no reference to the group
  as an index set survives.  Periodicity moves both directions, so a degree without cohomology has
  none two degrees higher and none two degrees lower, and an induction over the integers starting
  from the adjacent pair reaches everything: **a representation of a finite cyclic group whose
  invariants are all norms and whose norm-zero vectors are all differences has no complete
  cohomology in any degree whatsoever.**
* `InverseGalois.CFT.TateCohomology.Product` takes a family of representations indexed by an
  arbitrary set and forms the product on which the group acts one factor at a time.  A family is
  invariant exactly when each of its members is and the norm of a family is the family of the
  norms, so in degree zero the complete cohomology of the product is the product of the complete
  cohomologies.  A family of functions on the group is the same thing as a function on the group
  with values in the product, and under that identification the embeddings of the factors assemble
  into the embedding of the product and the summations of the factors into the summation of the
  product; so the product sits in two short exact sequences whose middle term is the functions on
  the group with values in the product, hence has no complete cohomology, and whose remaining terms
  are the products of the shifts and of the coshifts.  Running the resulting bijections in the two
  directions from degree zero gives **the complete cohomology of a product of representations as
  the product of their complete cohomologies, in every integer degree**, which is what turns a
  module built place by place into a product of local contributions.
* `InverseGalois.CFT.TateCohomology.Pair` specialises that to a product of two representations, a
  family indexed by the two booleans, and records the identification of a function on the booleans
  with a pair.  The group of ideles is a product of the local factors at the infinite places and
  those at the finite ones, two halves indexed by different sets, so its cohomology is only the
  product of the two contributions once this specialisation is available.
* `InverseGalois.CFT.TateCohomology.Annihilate` runs the two inductions those identifications
  allow, upwards from degree zero and downwards from degree minus one, and concludes that **the
  order of the group annihilates the complete cohomology in every integer degree**.
* `InverseGalois.CFT.TateCohomology.FreePresentation` presents an arbitrary representation by one
  whose underlying module is free: the free module on the elements of the representation, with the
  group permuting the generators, maps onto it by reading a formal combination of elements as the
  combination itself.  The construction costs nothing and is available for every representation,
  and it is what lets a theorem which asks the coefficients to be flat say something about
  coefficients which are not.
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
* `InverseGalois.CFT.TateCohomology.Shapiro` compares the complete cohomology of a group with
  coefficients coinduced from a subgroup with the complete cohomology of that subgroup.  An
  equivariant function is invariant exactly when it is constant, so evaluation at the neutral
  element identifies the invariants; the function supported on the subgroup carrying all the
  translates of a vector and the sum over a transversal of the classes of the values are mutually
  inverse on the coinvariants; and since the group is the product of a transversal and the
  subgroup, the norm of the group becomes the norm of the subgroup under that pair of maps.  A
  commuting square of that shape transports both middle Tate groups, and the ordinary cohomology
  above and the ordinary homology below are the two halves of Shapiro's lemma already available,
  the second through the isomorphism between the induced and the coinduced representation of a
  subgroup of finite index: **the complete cohomology of a coinduced representation is the complete
  cohomology of the representation it is coinduced from, in every integer degree.**
* `InverseGalois.CFT.TateCohomology.Restrict` carries those two maps to every degree.  A choice of
  coset representatives splits the group as the cosets times the subgroup, so the functions on the
  group, read on the subgroup, are the functions on the subgroup with values in the functions on
  the cosets, and therefore **still have no complete cohomology**; the connecting map of either
  shifting sequence is still bijective after restriction and moves a degree.  Since the same
  connecting maps are used on both sides, **corestriction after restriction is multiplication by
  the index in every integer degree**.
* `InverseGalois.CFT.TateCohomology.RestrictNatural` reads a map of representations on the subgroup
  and follows it through that construction.  In the two middle degrees the two transfers commute
  with any equivariant map, one term of the sum at a time; in every other degree the identifications
  used are connecting maps of the shifting sequences read on the subgroup, and a connecting map
  commutes with a map of short exact sequences.  So **restriction to a subgroup and corestriction
  from it both commute with a map of representations, in every integer degree**, which is what turns
  a comparison of coefficients into a comparison of the local and the global reading of a class.
* `InverseGalois.CFT.TateCohomology.RestrictShift` records the two recursions that define those maps
  as the statements they are.  In a nonnegative degree restriction is defined through the
  identification of the complete cohomology of the shift, and in a degree below minus one through
  the identification of the complete cohomology of the coshift, so **restriction commutes with the
  identification of the shift in every nonnegative degree and with the identification of the coshift
  in every degree below minus one**, and the same for corestriction, with nothing to prove in either
  range.  The two degrees left out are the two where the recursion has a base case rather than a
  step, and they are the only place where the comparison carries content.
* `InverseGalois.CFT.TateCohomology.RestrictDelta` supplies that content in the degree below zero.
  A class in degree minus one is represented by an element of the middle term whose norm comes from
  the sub, and the connecting map sends it to the class of that preimage; the transfer of such an
  element is again of that kind because the norm of the group is the transfer of the norm of the
  subgroup, and the preimage transfers along with it.  Reading the same computation in the two
  directions gives that **the connecting map in degree minus one commutes with restriction to a
  subgroup and with corestriction from it**, for an arbitrary short exact sequence of
  representations.  With the two recursions this is the base case that a comparison in a general
  degree rests on.
* `InverseGalois.CFT.TateCohomology.RestrictSplit` closes the square between restriction and the
  connecting map.  Reading a sequence on a subgroup is a functor and carries the identity on the sub
  to the identity, so a comparison of an extension with either defining sequence survives passage to
  a subgroup, and the connecting map of the restricted extension is the restricted comparison
  composed with the identification of the shift for the subgroup, and dually with the coshift.  Each
  of those two identifications commutes with restriction exactly in the range of degrees where it is
  the definition, and the two ranges together with the base case in the degree below zero leave
  nothing out.  Hence **restriction to a subgroup and corestriction from it both commute with the
  connecting map of an extension split as a sequence of modules, in every integer degree**.  Applied
  to the two defining sequences, which are split, this removes the restriction on the degree from
  the two identifications themselves: **both moves of the degree commute with restriction and with
  corestriction in every integer degree.**
* `InverseGalois.CFT.TateCohomology.RestrictShiftBridge` compares the two shifts a subgroup has.
  The shift of a representation read on a subgroup is still the functions on the whole group, while
  the shift of the representation read on the subgroup is the functions on the subgroup only: the
  second is not the first read on the subgroup, and there is a canonical map from the first to the
  second.  It is the comparison of a split sequence with the sequence defining a shift, for the
  splitting given by the value at the unit of the group and by subtracting the record of all the
  translates of that value, and on a function it restricts to the subgroup and subtracts those
  translates.  **The identification raising the degree by one on a subgroup is the identification of
  the restricted representation composed with that map**, and **the map commutes with the passage of
  the shift through a tensor product**, on the nose.
* `InverseGalois.CFT.TateCohomology.NakayamaRestrict` carries that square to the comparison of Tate
  and Nakayama.  The extension a cocycle tensors is a product as a sequence of modules, the tensor
  product being one coordinate and the coefficients the other, and read on a subgroup it is the
  extension the restricted cocycle tensors, on the nose; so **the connecting map of the tensored
  extension commutes with restriction to a subgroup and with corestriction from it**, in every
  integer degree.  The comparison is that connecting map followed by two identifications, the shift
  of a tensor product with the tensor product of the shift and the shift of the degree, and both of
  those commute with restriction and with corestriction as well.  Hence **the comparison of Tate and
  Nakayama attached to a class in degree two commutes with restriction to a subgroup and with
  corestriction from it**, the comparison on the subgroup being the one the restricted cocycle
  builds.  This is what lets a question about the comparison for the whole group be settled on a
  Sylow subgroup one prime at a time: corestriction from a Sylow subgroup is onto, and it carries
  the image of the comparison there into the image of the comparison here.
* `InverseGalois.CFT.TateCohomology.NakayamaSubgroup` identifies the comparison a subgroup inherits
  with the comparison it has of its own.  The cocycle of the shift read on the subgroup and the
  cocycle chosen on the subgroup both have, as their class in degree one, the restriction of the
  prescribed class in degree two; pushed along the comparison of the two shifts they are therefore
  cohomologous, and a map of representations carrying one cocycle to a cohomologous one carries the
  connecting map of one tensored extension to the connecting map of the other.  So **the comparison
  of Tate and Nakayama on a subgroup is the comparison of the subgroup**, for the representation
  read there and the restriction of the class.  The consequence is a local-to-global statement: if a
  representation of the subgroup maps to the representation of the group read there and carries a
  class in degree two of its own to the restriction of the prescribed class — as the units of a
  completion map to the idele classes and carry the fundamental class localised at a place to the
  restriction of the fundamental class — then **everything the comparison produces on the subgroup
  already comes from that representation**, so that a global obstruction read on a decomposition
  group is a local obstruction.
* `InverseGalois.CFT.TateCohomology.SylowInjective` draws the consequence that a class killed by
  restriction to a subgroup is killed by the index of that subgroup, so that **a class killed by a
  power of a prime and by restriction to a Sylow subgroup for that prime vanishes**: the study of
  the complete cohomology of a finite group reduces to its Sylow subgroups, one prime at a time.
* `InverseGalois.CFT.TateCohomology.SylowSurjective` reads the same relation in the other
  direction.  Writing one as a combination of the index of a subgroup and a multiple that kills a
  class, the term carrying the multiple disappears and the class is exhibited as a corestriction,
  so **a class killed by a natural number prime to the index of a subgroup comes from that
  subgroup**.  Coefficients killed by a power of a prime have complete cohomology killed by the
  same power, because the multiple of the identity that kills them induces that multiple on the
  cohomology; so **corestriction from a Sylow subgroup is onto the complete cohomology of
  coefficients killed by a power of that prime**, which is the surjectivity accompanying the
  injectivity of restriction.
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
* `InverseGalois.CFT.TateCohomology.TateNakayamaError` asks what happens when the tensored
  extension does have some.  The comparison is a map whatever the coefficients are, since it is
  built from the connecting map of the tensored extension and two isomorphisms; and the long exact
  sequence describes it completely, **its image being the classes that die in the tensored
  extension and its kernel the classes that come from there**.  So **the comparison is bijective
  as soon as the tensored extension has no complete cohomology in the two degrees that bound it**,
  rather than in all of them, and what measures the failure of the theorem of Tate and Nakayama is
  exactly the complete cohomology of the extension tensored with the coefficients, in those two
  degrees.  The comparison agrees with the isomorphism of the previous file wherever the latter is
  defined, so nothing that was proved with it has to be reproved.
* `InverseGalois.CFT.TateCohomology.NakayamaCoeff` asks how that comparison depends on the
  coefficients, the representation and the class staying fixed.  Nothing has to be corrected this
  time: the cocycle that builds the twisted extension belongs to the representation and not to the
  coefficients, so a map of coefficients extends to the two tensored extensions simply by acting on
  both coordinates, and that extension is equivariant as it stands.  It is a map of short exact
  sequences whose two outer components are the map of coefficients itself and the same map tensored
  with the representation, so the connecting maps agree; the comparison of the shift of a tensor
  product with the tensor product of the shift is natural in the second factor as well, and **the
  comparison of Tate and Nakayama attached to a class in degree two commutes with a map of
  coefficients**.  The consequence is what makes a free presentation of the coefficients useful:
  **if the comparison is onto for one set of coefficients, then everything the map of coefficients
  produces two degrees higher is already a value of the comparison for the target**, so the failure
  of the comparison to be onto is confined to the cokernel of the map a presentation induces.
* `InverseGalois.CFT.TateCohomology.NakayamaNatural` asks how that comparison depends on the
  representation it is attached to.  A map of representations carries a class in degree two to a
  class in degree two, but it carries the cocycle chosen for the first only to a cocycle
  cohomologous to the cocycle chosen for the second, and the difference is a coboundary.  That
  coboundary is precisely the correction that makes the obvious map of the two tensored extensions
  equivariant: the vector whose failure to be invariant is the difference is added to the tensor
  coordinate, and the corrected map is a map of short exact sequences which is the map of
  representations tensored with the coefficients on the sub and the identity on the quotient.  The
  connecting maps therefore agree, the comparison of the shift of a tensor product with the tensor
  product of the shift is natural, and **the comparison of Tate and Nakayama attached to a class in
  degree two commutes with a map of representations**, the class on the target being the image of
  the class on the source.  The consequence used later is a containment of images: **whatever the
  comparison produces for a class that comes from another representation already comes from that
  representation.**
* `InverseGalois.CFT.TateCohomology.NakayamaNextNatural` carries that naturality one step further
  along the long exact sequence.  The map that leaves the comparison is the map induced by the
  inclusion of the tensor product into the extension attached to the class, read through the
  identification of the shift of a tensor product with the tensor product of the shift and through
  the identification of the complete cohomology of a shift with that of the representation one
  degree higher; both identifications are natural, and the two extensions are compared by the very
  map that made the comparison natural, so **the map leaving the comparison commutes with a map of
  representations as well**.  What that buys is the only form in which the obstruction of Tate and
  Nakayama is computable: it is a map out of a group with no independent description, but **the
  values it takes on the classes coming from a second representation are exactly the image of the
  values the map of that second representation takes**, and the second representation may be a
  local one.  The identification of the target of the obstruction with the vectors killed by the
  prime is an isomorphism, so a spanning statement about the obstruction is the same statement
  about the map it is built from, where that naturality is available.
* `InverseGalois.CFT.TateCohomology.NakayamaNextRestrict` asks the same question of a subgroup
  rather than of a map of representations.  The two identifications of degree that the map leaving
  the comparison is read through both commute with restriction and with corestriction, and they are
  invertible, so their inverses do too; the induced map commutes with both by naturality.  Hence
  **the map leaving the comparison commutes with restriction to a subgroup and with corestriction
  from it**, and the consequence used later is again a statement about images: as soon as
  corestriction of the tensor product from the subgroup is onto, **whatever the map leaving the
  comparison reaches on the whole group is the corestriction of what it reaches on the subgroup**.
  That is what turns a question about a Sylow subgroup into a question about the places one at a
  time, since the classes coming from a product over the places are corestrictions from the
  stabilisers of the places.
* `InverseGalois.CFT.TateCohomology.DeltaShift` removes the connecting map from that comparison
  altogether.  The sequence defining the shift is the universal extension with acyclic middle term,
  and its connecting map is the identification of the complete cohomology of the shift with that of
  the representation one degree higher; so **the connecting map of an extension that compares with
  the shifting sequence is that identification composed with the map induced by the comparison in
  the third place.**  The tensored extension does compare with it, because it is a sum as a module:
  reading an element in the first entry of all of its translates is an equivariant map into the
  functions on the group, and modulo the translates of the tensor product the result depends only on
  the second entry, so the coefficients map to the shift of the tensor product by sending an element
  to the class of the function pairing the values of the cocycle with the moved element.  The
  outcome is that **the comparison of Tate and Nakayama is a composite of identifications of shifts
  and of maps induced by morphisms of representations**, with no connecting map left in it, so any
  statement already available for induced maps and for the identification of a shift reaches the
  comparison itself.
* `InverseGalois.CFT.TateCohomology.DeltaCoshift` does the same on the other side, which is what a
  negative degree needs.  The sequence defining the coshift of a representation has the functions on
  the group as middle term and the summation over the group onto the representation, and its
  connecting map is the identification of the complete cohomology of the representation with that of
  its coshift one degree higher.  An extension whose projection has a section as a map of modules
  compares with it: lifting the values of a function on the group and summing them after undoing the
  translation is an equivariant map into the middle term of the extension, compatible with the two
  projections because the section is one, and the identity on the quotient.  So **the connecting map
  of such an extension is the identification of the coshift followed by the map induced on the
  subs.**  The tensored extension is of that kind, its middle term being a product, so **the
  comparison of Tate and Nakayama is also a composite of induced maps and the identification of a
  coshift**, which is the expression a degree below the range the shift covers.
* `InverseGalois.CFT.TateCohomology.DeltaRetract` frees the first of those two comparisons from the
  tensor product it was written for.  All that the comparison with the shifting sequence uses is a
  retraction of the middle term of the extension onto its sub as a map of modules: reading all the
  translates of an element of the middle term through such a retraction is equivariant and restores
  the embedding of the sub, and modulo the translates of the sub the result depends only on the
  image in the quotient, because two elements with the same image differ by an element of the sub.
  So **the connecting map of an extension whose sub is a direct summand of its middle term is the
  map induced on the quotients followed by the identification of the shift**, for any extension
  split as a sequence of modules, the tensored one among them.
* `InverseGalois.CFT.TateCohomology.TensorFunctor` tensors a map of representations on the right
  with a fixed representation.  The underlying map acts on the first factor and leaves the second
  alone, and it commutes with the diagonal action because each factor is moved separately;
  composition and identities are respected factor by factor, so an isomorphism stays an isomorphism
  and a short complex stays a short complex.  Tensoring is right exact, so the map onto the
  quotient stays surjective and the image of the sub is still the whole kernel; the one thing that
  can fail is the injectivity of the map from the sub, and flatness of the fixed representation
  supplies exactly that.  So **a short exact sequence tensored with a flat representation is short
  exact**.
* `InverseGalois.CFT.Tate.TensorSplit` records what is left of injectivity when flatness is out of
  reach.  A map of representations with a left inverse is carried by any functor to a map with a
  left inverse, and a map with a left inverse is injective; complete cohomology in a fixed degree is
  such a functor and so is tensoring on the right, so **a map of representations that is a retract
  stays injective after tensoring, after passing to complete cohomology, and after both**.  That is
  what separates a local factor of the ideles from the units of its valuation ring once the
  coefficients are twisted, the vanishing available for untwisted coefficients being gone.
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
* `InverseGalois.CFT.TateCohomology.TorsionShift` factors multiplication by a natural number into
  two short exact sequences: the vectors it kills, the representation and its multiples, and then
  the multiples, the representation and the reduction.  Both have the representation itself in the
  middle, so when it has no complete cohomology at all both connecting maps are bijective and
  **the complete cohomology of the reduction in a degree is the complete cohomology of the vectors
  killed by the number two degrees higher.**  In particular **the reduction has no first cohomology
  as soon as those vectors have none in degree three**, which is what the previous file asks of the
  extension attached to the fundamental class.
* `InverseGalois.CFT.TateCohomology.TorsionInduced` takes the vectors killed by a number along the
  sequence defining the shift.  Taking them is a functor, and exactness on the left and in the
  middle survives at once; on the right it survives too, because the record of all the translates
  of a vector can be undone by reading off the value at the identity, so a function whose class in
  the shift is killed by the number can be corrected by the record of its own value at the identity
  into a function that is itself killed by the number.  The functions on the group with values in
  the vectors killed by the number are exactly the vectors killed by the number in the functions on
  the group, so the middle term still has no complete cohomology, over the group and over any of
  its subgroups, and **the complete cohomology of the vectors killed by a number in the shift is
  the complete cohomology of the vectors killed by that number one degree higher.**
* `InverseGalois.CFT.TateCohomology.TorsionNakayama` spends those two dimension shifts on the
  hypothesis left over above.  The extension attached to the fundamental class is cohomologically
  trivial on each Sylow subgroup, and the base ring has no torsion at the prime, so the vectors of
  the extension killed by the prime are the vectors of the shift killed by the prime.  Running the
  shift of the torsion and then the shift of the reduction, **the reduction modulo a prime of the
  extension attached to the fundamental class has no first cohomology on a Sylow subgroup for that
  prime as soon as the vectors of the representation killed by the prime have no complete
  cohomology there in degree four**, and **the theorem of Tate and Nakayama for coefficients killed
  by a prime holds under that hypothesis alone** -- a statement about the coefficients one starts
  from rather than about an auxiliary extension.
* `InverseGalois.CFT.TateCohomology.TensorPExact` keeps a short exact sequence exact when the
  coefficients are killed by a prime.  Tensoring preserves surjectivity and exactness in the
  middle whatever the coefficients are; only injectivity can fail, and it does not fail here.  A
  module killed by a prime is a vector space over the field with that many elements, so a subspace
  of it is a direct summand: **an injection into a module killed by a prime has a retraction**,
  additive rather than equivariant, and a retraction is all that survives of it into the tensor
  product.  So **a map into a representation killed by a prime stays injective after tensoring**
  with anything, and for a general map the same argument applies to its reduction modulo the
  prime, since tensoring with coefficients killed by a prime does not see the difference between a
  representation and its reduction.  Hence **a short exact sequence stays short exact after
  tensoring with coefficients killed by a prime as soon as its first map stays injective modulo
  that prime** -- and with no condition at all when its middle term is itself killed by the prime.
* `InverseGalois.CFT.TateCohomology.TensorRight` tensors in the other variable.  A map of
  coefficients, tensored on the left with a fixed representation, is again a map of
  representations, and composition and identities are respected factor by factor, so a short
  complex of coefficients is carried to a short complex.  Right exactness holds on either side, so
  again only injectivity can fail and flatness of the fixed representation supplies it: **a short
  exact sequence of coefficients tensored with a flat representation is short exact.**  Both
  variables are needed together, because a class formation sits in the first and the coefficients
  of an embedding problem sit in the second.
* `InverseGalois.CFT.TateCohomology.TensorTor` measures what is lost when the coefficients are
  presented.  Tensoring a representation with a presentation of the coefficients is right exact but
  not exact: the map from the sub of the presentation into its middle term need no longer be
  injective, and its kernel is **the first derived tensor product**, which vanishes as soon as the
  representation is flat.  Nothing else is lost, so the four terms are exact, and cutting them at
  the image of the middle map gives two short exact sequences with the tensor products with the sub
  and with the middle term in the middle.  Those two are acyclic whenever the representation is
  cohomologically trivial on every Sylow subgroup and the presentation is flat, so both connecting
  maps are bijective and **the complete cohomology of the tensor product with the coefficients in a
  degree is the complete cohomology of the first derived tensor product two degrees higher.**  That
  is exactly the correction to the theorem of Tate and Nakayama for coefficients which are not
  flat.
* `InverseGalois.CFT.TateCohomology.TensorPTorsionShift` computes that correction without ever
  forming a derived tensor product, by working in the first variable instead.  A presentation of a
  representation by one on which a prime acts without torsion, read modulo that prime, becomes four
  exact terms: the vectors of the quotient killed by the prime, the two reductions, and the
  reduction of the quotient.  Cutting them at the cycles gives two short exact sequences whose
  middle terms are reductions, hence killed by the prime, so both stay short exact after tensoring
  with any coefficients killed by the prime -- no flatness and no derived functor are needed.  What
  sits at the bottom is identified directly: a vector of the sub whose image is a multiple of the
  prime determines uniquely the vector of the middle term it is the multiple of, that vector has
  image killed by the prime in the quotient, every such image arises this way, and the vectors of
  the sub dying on either side are exactly the multiples of the prime, so **the lower kernel of a
  reduced presentation is the vectors of the quotient killed by the prime.**  Both connecting maps
  are then bijective whenever the two terms of the presentation are acyclic after tensoring, and
  **the complete cohomology of a representation tensored with coefficients killed by a prime, in a
  degree, is the complete cohomology of the vectors it kills, tensored with the same coefficients,
  two degrees higher.**  The free cover supplies a presentation for which the hypotheses hold as
  soon as the representation is cohomologically trivial on each Sylow subgroup for the prime.
* `InverseGalois.CFT.TateCohomology.TensorTorsionError` removes the hypotheses altogether, by naming
  what the comparison of Tate and Nakayama loses instead of asking that it lose nothing.  The
  comparison is built from a connecting map followed by two identifications, and identifications
  neither add to a kernel nor take from an image, so what the comparison kills is what the
  connecting map kills, and what dies just after it is what dies just after the connecting map.
  Those two are read off the long exact sequence of the extension by a cocycle: **the kernel of the
  comparison is the image of the term before it and its image is the kernel of the term after it**,
  and both of those terms are the extension tensored with the coefficients.  When the coefficients
  are killed by a prime that extension is the vectors killed by the prime, three and four degrees
  above, so **the comparison of Tate and Nakayama sits in four exact terms whose two ends are the
  vectors killed by the prime, tensored with the same coefficients** -- with no hypothesis at all
  beyond the classical one on the Sylow subgroups.  The isomorphism of the previous file is the
  case where the two ends vanish.
* `InverseGalois.CFT.TateCohomology.NakayamaSubgroupError` reads those four terms over a subgroup.
  A subgroup carries the restricted class, and the count that yields the classical hypotheses on the
  subgroups of the group yields them on the subgroups of a subgroup, so the four term exact sequence
  exists there with the representation and the coefficients read on the subgroup.  Its middle map is
  the comparison the subgroup inherits, which is the comparison of the subgroup itself.  Hence
  **what the comparison of Tate and Nakayama produces over a subgroup is exactly what the
  obstruction map of that subgroup kills**, and a spanning condition over a subgroup becomes a
  statement about one linear map defined there.
* `InverseGalois.CFT.TateCohomology.TorsionErrorLong` widens that window by one place.  The
  obstruction is, through the identification of the tensored extension with the vectors killed by
  the prime three degrees higher, the map induced by the inclusion of the tensor product into the
  extension, and the map that follows it in the long exact sequence is the one induced by the
  projection of the extension onto the coefficients -- which is, through the same identification,
  the map entering the comparison one degree higher.  Exactness of the long exact sequence at the
  middle term therefore says that **what the obstruction of Tate and Nakayama at a prime produces in
  a degree is exactly what the map entering the comparison one degree higher kills**, so the four
  term sequence extends to a long exact sequence alternating between the coefficients, their tensor
  product with the representation, and the vectors of the representation killed by the prime.  A
  statement about the image of the obstruction thereby becomes a statement about the kernel of an
  explicit map, over the group or over any subgroup of it.
* `InverseGalois.CFT.TateCohomology.TensorPi` lets the coefficients pass through a product.  A
  tensor product does not commute with an infinite product of groups, so a family of
  representations tensored with fixed coefficients is not in general the product of the tensored
  factors; it is, however, as soon as the coefficients are of finite rank over the field with a
  prime number of elements and every factor is killed by that prime.  A choice of coordinates on
  the coefficients multiplies a vector killed by the prime by a residue class, and **that
  multiplication is additive in the class precisely because the vector is killed by the prime**, so
  the coordinates assemble into a map from the group tensored with the coefficients to a finite
  power of the group.  Reading the coordinates back off the distinguished vectors inverts it, and
  **an abelian group killed by a prime, tensored with coefficients of finite rank over the field
  with that many elements, is a finite power of the group** -- naturally in the group.  Naturality
  compares the coordinates of a product with the coordinates of each factor and identifies the
  canonical map between them, so **a product of representations killed by a prime, tensored with
  such coefficients, is the product of the factors tensored with them**, and it has no complete
  cohomology in a degree in which no factor tensored with the coefficients has any.  For the ideles
  that is the whole point: the vectors killed by a prime are a product over the places, and this is
  what turns the obstruction to the comparison of Tate and Nakayama into a condition place by
  place.
* `InverseGalois.CFT.TateCohomology.TensorPair` reads that off for a module visibly built from two
  halves.  A product of two representations is a product of a family indexed by the booleans, so
  **the complete cohomology of a product of two representations killed by a prime, tensored with
  coefficients of finite rank over the field with that many elements, is the product of the
  complete cohomologies of the two factors tensored with the coefficients** — the group of ideles
  being exactly such a module, the infinite places and the finite ones.
* `InverseGalois.CFT.Tate.FamilyTensor` carries the coefficients through the orbit decomposition
  itself, and does it without ever unwinding that decomposition.  Tensoring each module of a family
  with a fixed representation, and letting the group act on both factors at once, gives another
  family over the same index set; **the sections of the tensored family are the sections of the
  original family tensored with the coefficients** whenever every module of the family is killed by
  a prime and the coefficients are of finite rank over the field with that many elements, by the
  same coordinates as for a product.  At a base point of an orbit the stabiliser sees the module
  there tensored with the coefficients restricted to it, so the orbit decomposition already proved
  for an arbitrary family applies verbatim to the tensored one, and **the sections of a family
  killed by a prime, tensored with such coefficients, have no complete cohomology in a degree as
  soon as no stabiliser has any with the restricted coefficients**.
* `InverseGalois.CFT.Tate.FamilyTensorOrbit` upgrades the vanishing to the identification behind
  it: **the complete cohomology of the sections of a family tensored with the coefficients is the
  product, over the orbits of the index set, of the complete cohomology of the stabiliser of a
  point of the orbit with coefficients in the module there tensored with the restricted
  coefficients**, and the same for the sections killed by the prime.  The vanishing follows, but a
  long exact sequence built out of these groups needs the isomorphism itself, so both are stated.
* `InverseGalois.CFT.Tate.FamilyTensorFull` removes the hypothesis that the modules of the family
  be killed by the prime, which the groups that actually occur do not satisfy: the units of the
  completions of a number field at its places are killed by nothing.  Only the coefficients need be
  finite.  A basis of the coefficients over the prime field writes every element of a tensor
  product as a sum of pure tensors along the basis vectors, and the element determines those
  coordinates up to multiples of the prime; divisibility by the prime is read in the quotient by
  the multiples of the prime, which is killed by the prime whatever the module, so the coordinate
  map available there detects it.  An element of the kernel therefore has all its coordinates
  divisible by the prime, and the prime moves across the tensor sign onto the basis vectors, where
  it kills them.  Hence **the sections of an arbitrary family tensored with coefficients of finite
  rank over the prime field are the sections of the tensored family**, and **the complete
  cohomology of those tensored sections is the product over the orbits of the local
  contributions** — which is the group of ideles, place by place, in its decomposition groups.
* `InverseGalois.CFT.Tate.FamilyTensorLocal` twists the detection of a class at the indices.  Since
  the coefficients pass through the sections, a class of the first cohomology of the twisted
  sections is a class of the sections of the twisted family, and the coboundary theorem for families
  applies to it; the local hypothesis it needs is the given one, because evaluation at an index
  commutes with tensoring and the twisted family at a fixed index is the module there tensored with
  the restricted coefficients.  So **a class of the first cohomology of the twisted sections
  vanishes as soon as, at every index, its restriction to the stabiliser followed by evaluation
  there vanishes** — the local-global statement the ideles need, with no isomorphism onto a
  coinduced module anywhere in it.
* `InverseGalois.CFT.Tate.ProdH1` cuts a representation into two pieces.  A pair of maps out of a
  representation whose combined effect is a bijection presents it as a product of the two targets,
  and in degree one the two coboundary witnesses of the two images assemble to a single element,
  which is a coboundary witness for the cocycle itself: **a class of the first cohomology vanishes
  as soon as both of its images do.**  The pair wanted is the two projections of a product of two
  modules acted on componentwise, and its twist by coefficients, which is available with no
  hypothesis on the two modules because a tensor product commutes with a product of *two* of them.
  The ideles of a number field are such a product, of the infinite places and the finite ones, and
  their local unit groups are killed by no integer, so this is the only form of the splitting that
  reaches them.
* `InverseGalois.CFT.Tate.FamilyTensorFinsupp` reads the support of such a tensored section.  The
  comparison with the sections of the tensored family is computed coordinatewise, so its value at
  an index is assembled from the values of the coordinates there and vanishes wherever all of them
  do: **coordinates of finite support assemble to an element whose comparison has finite support.**
  The converse is the useful direction and calls on the divisibility argument again — off the
  support the coordinates are divisible by the prime, and the prime moves onto the basis vectors of
  the coefficients, which it kills — so truncating the coordinates on the support changes nothing
  and **an element whose comparison has finite support is assembled from coordinates of finite
  support.**
* `InverseGalois.CFT.Tate.FamilyTrunc` corrects a section on a finite invariant set.  A section
  need not be fixed by the group, but it may fail to be fixed only in finitely many coordinates;
  enlarging those to an invariant set, which stays finite because the group is finite, and
  replacing the section by zero there produces a section that is fixed and differs from the
  original only in finitely many coordinates.  So **a section which the group moves only in
  finitely many coordinates differs by a section of finite support from a section the group
  fixes** — which says exactly that an invariant of the quotient of the product by the sections of
  finite support lifts to an invariant of the product.
* `InverseGalois.CFT.Tate.LiftInvariants` turns such a lifting into an injection.  In degree zero
  the complete cohomology is the invariants modulo the norms, so **a map of representations along
  which every invariant of the target lifts to an invariant of the source is surjective there**;
  and in a short exact sequence a degree in which the map induced by the quotient is surjective is
  a degree out of which the connecting map vanishes, so **the map induced by the inclusion of the
  sub is injective one degree above.**  Hence **a short exact sequence whose quotient has every
  invariant lifted to the middle term has the complete cohomology of the sub injecting into that
  of the middle term in degree one.**
* `InverseGalois.CFT.Tate.FamilyInvariant` builds the invariant section such an argument needs out
  of local data.  A section is fixed by the whole group exactly when its value at every index is
  carried to its value at the translated index, so it is enough to choose, at one index of every
  orbit, a value that the stabiliser there leaves alone: transporting it around the orbit is
  unambiguous because two group elements reaching the same index differ by a member of the
  stabiliser.  The values so obtained are transports of the chosen ones, so **a family whose value
  at each index can be chosen with a property preserved by the transports and fixed by the
  stabiliser there has an invariant section all of whose values have the property**, and the
  indices carrying such a value form an invariant set, so no invariance has to be assumed.
* `InverseGalois.CFT.Units.InvariantUniformizer` supplies that data for the local unit groups.  A
  uniformizer at a place is at best fixed by the decomposition group, never by the whole Galois
  group, which moves the place; what a whole family of them can satisfy is that an automorphism
  carrying one place to another carry the chosen uniformizer at the first to the chosen one at the
  second.  The decomposition group is exactly the stabiliser, so the previous construction applies,
  and **all but finitely many places carry a uniformizer fixed by their decomposition group**,
  since an element of the base field of valuation minus one at a place provides one and only the
  places dividing the different fail to admit such an element.  Hence **a Galois invariant section
  of the family of local unit groups whose value at each of those places is a uniformizer.**
* `InverseGalois.CFT.Units.IdeleValuationSplit` measures the quotient of the whole product of the
  local unit groups by the ideles.  An element of the product is an idele exactly when its vector
  of local valuations vanishes at all but finitely many places, and that vector is a section of the
  family with a copy of the integers at every finite place, equivariantly, an automorphism
  preserving the valuation while moving the place.  Raising the invariant family of uniformizers to
  a given vector of integers is a right inverse of it, equivariant for the same reason, so
  **subtracting off the vector of valuations leaves an idele** and **the ideles, the whole product
  and the quotient form a short exact sequence of representations** in which **the inclusion of the
  ideles stays injective modulo a nonzero integer** — the integers having no torsion — so the
  sequence survives tensoring with coefficients that are not flat.
* `InverseGalois.CFT.Units.IdeleFullCompare` assembles the comparison.  Coefficients of finite rank
  over a prime field pass through the sections of the family of integers, so after tensoring with
  them finiteness of support is still read place by place, and an element of the tensored product
  all of whose Galois translates differ from it by ideles has a vector of valuations which the
  Galois group moves in finitely many places only.  Clearing that vector on the finite invariant
  saturation of those places and feeding the result back through the invariant uniformizers
  produces **an invariant element of the tensored product differing from the original one by an
  idele**, which is the lifting of invariants the previous file asks for.  Hence **the twisted
  complete cohomology of the ideles in degree one injects into that of the product of all the local
  unit groups** — so a class trivial on every decomposition group, which by the orbit decomposition
  is a class trivial in the whole product, is already trivial in the ideles.
* `InverseGalois.CFT.Units.IdeleLocalVanish` draws that conclusion.  The product of all the local
  unit groups is a product of the infinite places and the finite ones, so a class of its twisted
  first cohomology vanishes as soon as both of its projections do; and each half is the sections of
  a family indexed by the places of that kind, where a twisted class is detected at the indices.
  Restriction to the decomposition subgroup of a place commutes with reading the ideles at the
  places of one kind, so the local hypothesis at a place is exactly the local hypothesis the
  detection theorem wants there.  Chaining the three steps with the injection of the previous file
  gives **a class of the first cohomology of the twisted ideles that is trivial in every
  decomposition subgroup is trivial** — the local-global statement in the form the Shafarevich
  tower consumes, with no isomorphism onto a coinduced module used anywhere along the way.
* `InverseGalois.CFT.Units.GlobalUnitsLocal` reads the units of the field themselves that way.  A
  unit becomes an idele on the diagonal and an idele has a component at every place, and the whole
  passage from the one to the other is transparent: the diagonal is defined componentwise, the
  ideles sit inside the product of the local unit groups by inclusion, each half of that product is
  a projection, and evaluating a section at an index is evaluation.  So **the twisted units read in
  the decomposition subgroup of a place and evaluated there are the embedding of the units into the
  completion, tensored with the identity of the coefficients** — a map the comparison of a
  decomposition subgroup with a completion knows how to annihilate — and chaining that with the
  previous file gives **a class of the first cohomology of the twisted units whose local class
  vanishes at every place dies in the ideles.**
* `InverseGalois.CFT.Units.KummerIdele` supplies those local hypotheses for a class coming from
  Kummer theory, and so closes the passage from an everywhere locally trivial class of the
  transgression cohomology to the ideles.  A place of the level is met by a place of the whole
  extension above it, whose decomposition subgroup is the group fixing a level of its own; the
  compositum of that level with the Kummer level is where the local argument lives, Kummer data
  ascending to it and the units of the level surjecting onto its units with the coefficients
  attached, while a tensor killed there is read at the place as zero.  The arithmetical criterion
  for a locally trivial class then applies at each finite and each infinite place, the comparison
  of a stabiliser of a place of the level with a quotient of a stabiliser upstairs being the one
  identification the criterion needs.  Feeding the two families of local vanishings to the
  detection theorem of the previous file gives **the class of the twisted units attached to an
  everywhere locally trivial Kummer class dies in the ideles.**
* `InverseGalois.CFT.Units.KummerShaBot` draws the conclusion.  A class that dies in the ideles is
  produced by the comparison of Tate and Nakayama out of the complete cohomology of the coefficients
  three degrees lower, as soon as that comparison spans together with the classes coming from the
  ideles; so if the coefficients have no complete cohomology in degree minus two there is nothing
  for the class to be produced from, and it is trivial.  The reading of a locally trivial class over
  the Galois group of the level is injective, so **the everywhere locally trivial classes of a level
  are all trivial** under those two conditions — one a statement about the extension alone, the
  other about the group alone, and neither about the lifting problem.
* `InverseGalois.CFT.Tate.FamilyResGroup` observes that all of this is available on a subgroup of
  the acting group with nothing to prove.  A subgroup moves the index set by the restricted action
  and transports the modules by the same isomorphisms, so it acts on the same family; the sections
  are the same sections, carrying the restriction of the action of the whole group, and so are the
  sections killed by an integer.  **The orbit decomposition therefore holds over every subgroup**,
  with the orbits of the subgroup in place of the orbits of the group and the stabiliser in the
  subgroup in place of the stabiliser in the group.  That is what a criterion formulated over a
  Sylow subgroup asks for: the group of a Sylow subgroup moves the places of an extension in orbits
  finer than the places of the base field, and the stabiliser at one of them is the intersection of
  the subgroup with the decomposition group there.
* `InverseGalois.CFT.Units.IdeleTorsionTensor` is that statement for the ideles.  The elements of
  the ideles killed by a prime are the elements killed by it of the whole product of the local unit
  groups, the product splits into the infinite places and the finite ones, and each half is the
  sections of a family of modules over the places of the extension, so the previous files combine
  into **the complete cohomology of the elements of the ideles killed by a prime, tensored with
  coefficients of finite rank over the field with that many elements, as the product over the
  places of the base field of the complete cohomology of the decomposition group of a place above
  it with coefficients in the roots of unity of the completion there tensored with the restricted
  coefficients** — and in particular the vanishing of the whole as soon as every local factor
  vanishes.  That is the hypothesis the local-global obstruction of the theory of tori is stated
  with, now genuinely local.
* `InverseGalois.CFT.Units.IdeleTorsionSubgroup` says the same over a subgroup of the Galois group.
  A subgroup does not fix the places of the base field: it moves the places of the extension in
  orbits of its own, generally finer, and the stabiliser at one of them is the intersection of the
  subgroup with the decomposition group there.  Nothing new has to be computed, because the units of
  the completions are a family of modules on which the subgroup acts by the restricted action, and
  the only point to identify is that the transport by an element of the subgroup fixing a place is
  the transport by that element of the whole group.  So **the complete cohomology of a subgroup with
  coefficients in the elements of the ideles killed by a prime, tensored with coefficients of finite
  rank over the field with that many elements, is the product over the orbits of the subgroup on the
  places of the extension of the complete cohomology of the stabiliser there with coefficients in
  the roots of unity of the completion tensored with the restricted coefficients** — which is what a
  criterion formulated over a Sylow subgroup asks for.
* `InverseGalois.CFT.Units.IdeleClassTorsionSubgroup` passes from the ideles to the idele classes
  there.  A short exact sequence of representations stays short exact when read on a subgroup,
  because injectivity, surjectivity and exactness in the middle are statements about the underlying
  modules and those do not change, so the roots of unity of the field, the ideles killed by a prime
  and the idele classes killed by that prime still give a long exact sequence of complete cohomology
  of the subgroup.  **The idele classes killed by the prime therefore have no complete cohomology
  over the subgroup in a degree in which no local factor has any and the roots of unity of the field
  have none one degree higher**, the local factors being indexed by the orbits of the subgroup on
  the places of the extension.
* `InverseGalois.CFT.Units.IdeleClassTorsionSubgroupLocal` turns that vanishing statement into a
  presentation.  Exactness in the middle of the same long exact sequence says that **a class of the
  idele classes killed by a prime, tensored with the coefficients and read on a subgroup, is the
  image of a family of local classes exactly when the connecting map kills it**, one member of the
  family for each orbit of the subgroup on the places of the extension; and the connecting map lands
  in the roots of unity of the field, so **every class comes from such a family as soon as those
  carry no complete cohomology over the subgroup one degree higher**.  The presentation is stated
  for the target of the obstruction to the theorem of Tate and Nakayama as well: the vectors killed
  by a number inside the representation attached to an action are the elements killed by that number
  for the action, so the obstruction over a subgroup lands in a group presented entirely by local
  data.  That is the shape in which the criterion for the everywhere locally trivial classes of the
  units, read on a Sylow subgroup, is waiting to be checked.
* `InverseGalois.CFT.TateCohomology.Duality` pairs the two middle degrees against each other.  The
  functionals on a representation with values in a fixed module carry an action of the group
  through the source, and **the norm of such a functional is its composition with the norm of the
  representation**, because summing over the group is the same as summing over its inverses.  That
  one identity is the whole of the duality: an invariant functional is constant on the orbits, so
  it descends to the coinvariants, and it kills the norms, so evaluation on the classes of
  vanishing norm does not see the functionals that are themselves norms.  What comes out is a map
  from the complete cohomology in degree zero of the functionals to the functionals on the complete
  cohomology in degree minus one, and **that map is bijective as soon as the coefficients receive
  every functional defined on the norms and every functional defined on the vectors of vanishing
  norm**.  Injectivity is one extension: a functional killing the classes of vanishing norm factors
  through the norms, and an extension of that factor has the given functional as its norm.
  Surjectivity is the other: a functional read on the vectors of vanishing norm extends, and the
  extension is already invariant, since the difference of a vector and one of its translates has
  vanishing norm and trivial class.  Coefficients killed by a prime supply both extensions with
  nothing further, by the retraction of the previous file, so **a representation killed by a prime
  is dual to itself in the two middle degrees against any coefficients whatsoever**.  This is the
  base case from which the shift of degree carries the duality to every pair of degrees adding to
  minus one.
* `InverseGalois.CFT.TateCohomology.DualityShift` carries it there.  A function on the group with
  values in the functionals on a module is read as the functional summing the values its members
  take on the values of a function on the group, and **that reading is a bijection which respects
  the action**.  Under it the two constructions of the shift trade places: the summation map of the
  functionals becomes precomposition with the record of the translates, and the record of the
  translates of the functionals becomes precomposition with the summation map.  So **the coshift of
  the functionals is the functionals on the shift**, with nothing asked, and **the shift of the
  functionals is the functionals on the coshift** as soon as a functional defined on the vectors of
  vanishing sum extends to all the functions on the group -- again free when the representation is
  killed by a prime.  Since the complete cohomology of a shift in a degree is the complete
  cohomology of the representation one degree higher, those two identifications move the degree of
  the functionals up and down at will, and both moves preserve being killed by a prime.  An
  induction over the integers starting from the two middle degrees therefore reaches every degree:
  **the complete cohomology of the functionals on a representation killed by a prime, in any
  degree, is the group of functionals on the complete cohomology of the representation in the
  complementary degree.**
* `InverseGalois.CFT.TateCohomology.DualityDivisible` removes the hypothesis on the representation.
  The duality asks of the coefficients only that they receive every functional defined on a
  submodule, and for coefficients in which every element is divisible by every integer that is the
  criterion of Baer rather than a condition on the module the submodule sits in.  So **a divisible
  group of coefficients is dualizing for every representation of a finite group whatsoever**, and
  in particular, the circle of the rationals being divisible, **the characters of the complete
  cohomology of a representation in a degree are the complete cohomology of the characters of the
  representation in the complementary degree** -- the duality of Tate for a finite group, with no
  hypothesis on the representation and none on the degree.
* `InverseGalois.CFT.TateCohomology.DualityNatural` compares the duality for two representations.
  A map of representations reads a functional on the target as a functional on the source, and that
  reading is again a map of representations, in the opposite direction.  Each of the three pieces
  the duality is assembled from respects it: the pairing of the two middle degrees evaluates a
  functional on the image of a representative either way round, and the two identifications that
  move the degree both come down to the same sum of values.  Since the recursion over the integers
  is a chain of those moves, **the duality is compatible with every map of representations in every
  degree**: dualizing a class and restricting the functional along the map gives the same
  functional as moving the class along the dual map and dualizing there.  That is what a duality
  statement about an image needs, because a class lies in the image of a map exactly when every
  functional killing the image kills it, so a question about the image of one map turns into a
  question about the kernel of the map the duality attaches to it.
* `InverseGalois.CFT.TateCohomology.Pontryagin` counts the characters of a finite commutative group
  and recovers the group from them.  A cyclic group of an order has as many characters as the
  circle of the rationals has elements killed by that order, and those elements are the multiples
  of the reciprocal of the order, an element of exactly that order; so **a cyclic group has as many
  characters as elements**, and since the characters of a finite product are the products of the
  characters, the structure theorem for finite commutative groups gives the same count in general.
  Reading an element as the functional "evaluate at me" is then injective, a nonzero element being
  detected by some character, and an injection between finite sets of the same size is a bijection:
  **a finite commutative group is the characters of its characters.**
* `InverseGalois.CFT.TateCohomology.DualityFinite` turns that recovery into a statement about
  complete cohomology.  The evaluation of a representation in the functionals on its functionals is
  a map of representations, compatible with every map of representations, and for a representation
  with finitely many vectors it is an isomorphism; complete cohomology carries an isomorphism to a
  bijection, so composing with the duality identifies **the classes of a representation with
  finitely many vectors, in any degree, with the characters of the classes of its functionals in
  the complementary degree** -- and that identification too is compatible with every map of
  representations.  Because the circle of the rationals receives every functional defined on a
  submodule, the identification is more than a count: **every character of a submodule of the
  complete cohomology of the functionals is the pairing against some class of the complementary
  degree**, which is the form a duality argument takes when the submodule is the part of the
  cohomology cut out by conditions at the places and one wants a single class inducing a prescribed
  functional on it.
* `InverseGalois.CFT.TateCohomology.CyclicDual` applies that to the two representations of maps
  attached to a pair, one of which is cyclic.  Fix a representation whose vectors form a finite
  cyclic group and a second representation killed by the order of the first.  Composing a map into
  the cyclic representation with a map out of it produces an endomorphism of the cyclic group;
  evaluating that endomorphism at a generator turns it into a vector of the second representation,
  and an injective character of the cyclic group -- the identification of a finite cyclic group
  with the elements of the rational circle killed by its order -- reads the vector off as a value
  in the circle.  The pairing so obtained is a bijection for a reason that needs no counting:
  evaluation at a generator already identifies the maps out of the cyclic representation with the
  vectors of the second, and composing with the character already identifies the maps into the
  cyclic representation with the characters of the second, so the pairing is a composition of two
  bijections.  It respects the action because **the endomorphisms of a cyclic group commute with
  one another**, which makes conjugating a composite by a group element leave it unchanged.  So
  **the maps into a cyclic representation are the functionals on the maps out of it**, and feeding
  that isomorphism to the duality of the previous file gives **a duality between the complete
  cohomology of the maps out of a cyclic representation in one degree and the complete cohomology
  of the maps into it in the complementary degree** -- in every degree, and again in the strong
  form that every character of a submodule is the pairing against a single class.  Taking the
  cyclic representation to be the roots of unity of a prime order, the maps out of it are a twist
  and the maps into it are the dual in the sense of Cartier, so this is the duality that turns a
  statement about classes of the dual into a statement about classes of the twist.
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
* `InverseGalois.CFT.TateCohomology.RestrictTrans` carries that count down one more step, from the
  subgroups of a group to the subgroups of a subgroup.  A subgroup of a subgroup is a group of
  elements of the subgroup, and its image in the ambient group is a group of elements of that
  group; the two differ by the proof of membership each element carries, so they are isomorphic and
  a representation read on either of them is read along the same homomorphism.  **The complete
  cohomology of a subgroup of a subgroup is therefore the complete cohomology of its image**, in
  every degree, and the count made for the subgroups of the group is a count for the subgroups of a
  subgroup.  The remaining hypothesis needs no transport at all, the order of a restricted class
  being controlled by the order of the class one started with, so **the classical hypotheses of
  Tate's theorem for a class restricted to a subgroup hold on every subgroup of that subgroup** --
  which is what lets a construction available for a group with a fundamental class be run over a
  subgroup of it.
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
* `InverseGalois.CFT.Units.IdeleTorusSha` spends that theorem on the local-global obstruction of a
  torus.  Tensoring the sequence of the units, the ideles and the idele classes with a
  representation flat over the integers leaves it exact, so the long exact sequence of complete
  cohomology reads the classes of the units which die in the ideles as the image of the connecting
  map coming out of the idele classes one degree lower; and the theorem of Tate and Nakayama turns
  the idele classes in that degree into the representation itself two degrees lower.  Those classes
  are the everywhere locally trivial ones, since by Shapiro's lemma the cohomology of the ideles is
  the product of the cohomologies of the completions, so **the everywhere locally trivial part of
  the complete cohomology of the units tensored with a lattice, in degree `n + 3`, is exactly the
  image of the complete cohomology of the lattice in degree `n`**.  In degree one, that is the
  degree `-2` of the lattice: a finite object, where the cohomology of the units is not.  Every
  Galois extension of number fields carries a fundamental class, so the statement holds with no
  hypothesis on the extension beyond flatness of the lattice.
* `InverseGalois.CFT.Units.IdeleTensorTorsion` removes the flatness.  Coefficients killed by a prime
  are not flat, and exactly one thing can go wrong: the principal ideles might not stay injective
  after tensoring.  They do.  Tensoring with coefficients killed by a prime does not distinguish a
  module from its reduction modulo that prime, so the question is whether a unit of the field whose
  principal idele is a power of an idele is a power in the field; reading the equation at each place
  makes it a power in every completion, and for a prime exponent Wang's theorem makes it a power in
  the field.  So **the principal ideles stay injective modulo a prime**, and **the units, the ideles
  and the idele classes stay short exact after tensoring with coefficients killed by a prime**.  For
  the elements killed by the prime nothing has to be checked at all: there the middle term is itself
  killed by the prime, and an injection into such a module has a retraction which survives any
  tensoring.
* `InverseGalois.CFT.Units.IdeleTensorSha` reads the two long exact sequences that result.  In every
  degree, **the locally trivial classes of the units tensored with coefficients killed by a prime
  are exactly the image of the connecting map** coming out of the complete cohomology of the idele
  classes tensored with the same coefficients, one degree lower; so they vanish as soon as that
  cohomology does, with no hypothesis on the extension beyond finiteness of its Galois group.  The
  same reading applies to the elements of the three groups killed by the prime, and there it
  measures the failure of the theorem of Tate and Nakayama for coefficients with torsion, the
  elements of the idele classes killed by the prime being the first derived tensor product of the
  idele classes with such coefficients.
* `InverseGalois.CFT.Units.NsmulTorsionRep` reconciles the two names the development gives to the
  vectors killed by a number.  The general machinery reads them as the kernel of multiplication by a
  natural number inside a representation; the idele side reads them as the representation carried by
  the elements of an abelian group killed by an integer, for the induced action.  Multiplying by a
  natural number is multiplying by the corresponding integer, so the two subgroups have the same
  elements and the same action, and **the two descriptions are the same representation**.  The
  identification survives tensoring with any coefficients, so a vanishing computed on the roots of
  unity of the completions can be handed to the machinery for the elements a prime kills, and back.
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
* `InverseGalois.CFT.Brauer.CyclicGenerator` records how the invariant reacts to a change of the
  generator of the cyclic group.  Writing a second generator as a power of the first, the discrete
  logarithms differ by that power, so the two carry cocycles differ by the coboundary built from
  the integer part of the rescaled discrete logarithm.  Hence **raising the scalar to the same
  power leaves the Brauer class of a cyclic algebra unchanged**, and therefore **the invariant
  taken with respect to a power of a generator is the corresponding power of the invariant**; in
  particular the invariant with respect to an arbitrary generator of an unramified extension is a
  power of the Frobenius invariant.
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
* `InverseGalois.CFT.Units.BaseFundamentalCyclic` closes the two inequalities against each other.
  The second cohomology of the idele class group has at most as many elements as the Galois group,
  by the dévissage through cyclic extensions, and the fundamental class is annihilated by exactly
  the multiples of the degree, so the subgroup of its multiples already has at least that many.
  Hence **the second cohomology of the idele class group of a Galois extension of number fields is
  cyclic of order exactly the degree, generated by the fundamental class**, and any class with the
  same annihilator generates it too — the annihilator alone pins the class down up to a multiple
  prime to the degree.
* `InverseGalois.CFT.Units.BaseTateCoeff` puts the flat case to work on coefficients which are not
  flat.  The comparison of Tate and Nakayama is natural in the coefficients and is onto whenever
  they are flat, so **everything a map out of a flat representation induces two degrees higher is
  already a value of the comparison for the target**; the free presentation of the coefficients
  supplies such a map for free.  The criterion for the locally trivial classes therefore loses its
  reference to the obstruction altogether: **the everywhere locally trivial classes of the units
  tensored with coefficients killed by a prime are exactly the image of the complete cohomology of
  the coefficients three degrees lower as soon as the classes of the idele classes tensored with
  the coefficients are spanned by those the free presentation produces together with those coming
  from the ideles.**  The same file reads the spanning condition on a Sylow subgroup for the prime,
  corestriction from such a subgroup being onto on coefficients killed by it.
* `InverseGalois.CFT.Units.BaseTateSylow` makes that Sylow condition explicit.  The fundamental
  class of the idele class group satisfies the count on every subgroup of the Galois group, hence on
  every subgroup of a Sylow subgroup, so the obstruction of Tate and Nakayama at the prime is
  defined over that Sylow subgroup and **what the comparison produces there is exactly what it
  kills**.  The condition the locally trivial classes ask for therefore becomes a statement about a
  single linear map over the subgroup: **the everywhere locally trivial classes of the units
  tensored with coefficients killed by a prime are exactly the image of the complete cohomology of
  the coefficients three degrees lower as soon as the obstruction of a Sylow subgroup for that prime
  takes no value on the idele classes that it does not already take on the ideles** -- the shape a
  duality theorem has to take, now placed over a field over which the extension has degree a power
  of the prime.  The values that obstruction takes at all are the kernel of the map entering the
  comparison one degree higher, so the condition can also be read entirely inside the vectors of the
  idele classes killed by the prime, tensored with the coefficients, as the equality of one image
  with one kernel there.  The identification of the target of the obstruction with those vectors is
  an isomorphism, so the whole criterion may equally be stated for the map the obstruction is built
  from -- the form in which it is natural in the representation, hence the form in which its values
  can be compared with local ones.
* `InverseGalois.CFT.Units.BaseTateTorsion` drops the flatness, which the coefficients of an
  embedding problem never have.  The fundamental class satisfies the classical hypotheses on every
  subgroup, so in particular on every Sylow subgroup, and the four exact terms attached to the
  comparison apply verbatim: **the comparison of Tate and Nakayama for the idele class group of a
  Galois extension of number fields, for coefficients killed by a prime, is exact on both sides
  against the idele classes killed by that prime, tensored with the same coefficients**, three and
  four degrees above.  It is therefore an isomorphism exactly when those two groups vanish, and
  they are local: the idele classes killed by a prime sit between the units and the ideles, so the
  two conditions descend to a product over the places of the roots of unity of the completions and
  to the roots of unity of the field.
* `InverseGalois.CFT.Units.IdeleTorusShaTorsion` spends that on the local-global obstruction, for
  coefficients an embedding problem can supply.  The comparison of Tate and Nakayama, followed by
  the connecting map of the sequence of the idele classes, carries the complete cohomology of
  coefficients killed by a prime into the classes of the units tensored with them three degrees
  higher which die in the ideles -- the everywhere locally trivial ones, the cohomology of the
  ideles being a product over the places.  What that composite reaches is exactly what the
  connecting map produces from the idele classes on which the obstruction vanishes, and that is
  unconditional; when the obstruction group has no complete cohomology in the degree at hand,
  **the everywhere locally trivial classes of the units tensored with coefficients killed by a
  prime are exactly the image of the complete cohomology of the coefficients three degrees lower**,
  a finite object where the cohomology of the units is not.
* `InverseGalois.CFT.Units.IdeleTorusShaLocal` reads that obstruction one place at a time, which is
  what the decomposition of the ideles killed by a prime makes possible.  Most places cost nothing:
  the roots of unity of a completion are killed by the prime while the complete cohomology of a
  decomposition group is killed by its order, so **a place whose decomposition group has order prime
  to the prime contributes nothing at all.**  The decomposition group of an archimedean place has
  order one or two, so for an odd prime every archimedean place is of that kind and drops out, and
  what is left of the criterion is a condition at the finite places together with one on the roots
  of unity of the field.
* `InverseGalois.CFT.Units.IdeleTorusShaSharp` turns the sufficient condition into a necessary and
  sufficient one, which matters because the obstruction group does not vanish in general.  The image
  of a submodule under a linear map is everything the map reaches exactly when the submodule and the
  kernel together span, and the kernel of the connecting map is what comes from the ideles, so
  **the everywhere locally trivial classes of the units tensored with coefficients killed by a prime
  are exactly the image of the complete cohomology of the coefficients three degrees lower precisely
  when the obstruction of Tate and Nakayama takes no value on the idele classes that it does not
  already take on the ideles.**  The units and the locally trivial classes have disappeared from the
  criterion; what is left is a statement about the obstruction and the places.
* `InverseGalois.CFT.Units.NakayamaSpan` gives that criterion a name.  Read over a Sylow subgroup
  for the prime, and with the obstruction traded for the comparison it measures, what remains is a
  single span: **the classes the comparison of Tate and Nakayama produces, together with the
  classes coming from the ideles, fill the complete cohomology of the idele classes tensored with
  coefficients killed by the prime.**  For coefficients that are free as abelian groups the
  comparison is surjective by itself and the span holds for nothing; for coefficients killed by a
  prime it is the assertion that the failure of surjectivity is carried by the places.  Naming it
  separates what the general theory of a class formation supplies from what is genuinely about the
  arithmetic of the extension, and a Sylow subgroup exists because the Galois group is finite, so
  **the everywhere locally trivial classes of the units tensored with coefficients killed by a
  prime are exactly the image of the complete cohomology of the coefficients three degrees lower**
  whenever the span holds, with no subgroup left in the statement.  Read as a surjection and
  specialised to degree minus two, that is the shape an embedding problem asks for: the first
  cohomology of the units tensored with the coefficients, cut down by the condition of being
  trivial in the ideles, is reached from two degrees below zero.  **The span holds whenever the
  prime does not divide the degree of the extension**, since a Sylow subgroup is then trivial and
  the order of a group annihilates its complete cohomology, so nothing is left to span.
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
* `InverseGalois.CFT.Profinite.Coeff` composes a cochain with a homomorphism of the coefficients
  commuting with the two actions.  The cocycle relations are equations built from the group law and
  the action, so they are preserved, and a cochain constant on the cosets of an open normal
  subgroup stays constant there, so smoothness is preserved; a coboundary goes to the coboundary of
  the image of its primitive.  So **there is a homomorphism of the cohomology of the source
  coefficients into that of the target**, in degree one and in degree two, computed on cocycles.
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
* `InverseGalois.CFT.Profinite.Transgression` supplies what degree two needs beyond that reading.
  A class restricting trivially to the kernel is not yet constant on its cosets: it has to be
  corrected by successive twists, and the correction is only available once the transgression of
  the twisted cocycle is a coboundary.  Each of the four corrections is built by decomposing an
  element along its coset, so each is constant along any normal subgroup of the kernel acting
  trivially along which its own data is constant, and the corrected cocycle is then smooth.  The
  order matters: the subgroup for the first two corrections is read off the cocycle and its
  trivialisation, while the last two need a smaller one, cut out by the trivialisation of the
  transgression that the first two produce.  Shrinking twice gives **a smooth class whose
  restriction to the kernel and whose transgression are trivialised by smooth cochains is inflated
  from the quotient.**
* `InverseGalois.CFT.Profinite.TransgressionClass` reads the hypothesis that argument leaves over as
  a single cohomology class.  A transgression is uniformly smooth, is a homomorphism on the kernel,
  is a one cocycle for conjugation, and depends only on the coset of its index; those four
  conditions are exactly what makes it a smooth one cocycle of the group with values in the first
  cohomology of the kernel.  The kernel acts trivially on the coefficients, so that cohomology is
  the group of smooth homomorphisms and two cohomologous cocycles there are equal, which turns the
  trivialisation of a transgression into the vanishing of its class.  One step is not formal: the
  homomorphism the vanishing provides lives on the kernel and is extended by the unit outside, and
  the extension is smooth only if the homomorphism kills an open normal subgroup of the whole group.
  **A compact group has a basis of such subgroups**, its open subgroups being closed of finite
  index, and with that in hand the Hasse principle asked for becomes **the vanishing of those
  classes of the first cohomology of the group with values in the first cohomology of the kernel
  which are locally coboundaries.**
* `InverseGalois.CFT.Profinite.TransgressionRestrict` says the same of the local condition itself.
  Restricting both variables of a transgression to a subgroup leaves the four conditions standing,
  with respect to the part of the kernel lying inside that subgroup, so **a transgression restricts
  to a transgression of a subgroup** and has there a class of its own.  A trivialisation on the
  subgroup is a homomorphism on that part and is smooth there, which is precisely what makes the
  restricted class vanish, so the local hypothesis is one cohomology class per member of the family
  and nothing else: **a locally trivial class of the second cohomology whose restriction to the
  kernel is trivial is inflated from the quotient as soon as a transgression whose restricted
  classes all vanish has itself a vanishing class.**  Only that direction is used, so the members of
  the family are not asked to have a basis of open normal subgroups of their own.  Restricting a
  class and localising its coefficients at the same time is a homomorphism, and the restricted class
  of a transgression is the localisation of its class, so the hypothesis is the vanishing of a
  single group: **the everywhere locally trivial classes of the first cohomology with values in the
  first cohomology of the kernel.**  That is the group a local-global principle one degree down
  computes, and with it the descent has the shape arithmetic delivers.
* `InverseGalois.CFT.Profinite.Quotient` names a *level*: an open normal subgroup which acts
  trivially on the coefficients.  The quotient by it acts, and is discrete, and the projection to it
  has open kernel, so composing with the projection is **inflation from that level**, injective in
  degree one and hitting every class represented there in either degree.  The levels are cofinal for
  a trivial reason: smoothness of a cochain is constancy on the cosets of an open normal subgroup
  and smoothness of the action is triviality on one, and the intersection of the two is again open
  and normal, so **every class of either degree is represented at a level.**
* `InverseGalois.CFT.Profinite.QuotientAction` does the same for coefficients written additively.  A
  tensor product of two modules over a group is an additive group and there is no writing it
  otherwise, so the passage to the quotient has to be available in that notation too: **a subgroup
  each of whose elements fixes every point of an additive module lets the quotient by it act**, and
  the action of the quotient is the one for which the projection is equivariant.  The two forms are
  used side by side, the coefficients of a lifting problem and their cohomology multiplicatively and
  the tensor product which computes that cohomology additively.
* `InverseGalois.CFT.Profinite.TransgressionInflate` puts the descent at that level.  A
  transgression indexed by the unit satisfies the cocycle condition there, which says its value is
  its own square, so it is trivial; and the family depends only on the class of its index, so **a
  transgression indexed by an element of the kernel is trivial** and the cochain it defines is
  trivial on the kernel.  The kernel also acts trivially on the coefficients, so **the class of a
  transgression is inflated from the quotient**, and inflation is injective in degree one, so
  nothing is lost by asking for its vanishing there.  Localising an inflated class is inflating its
  localisation — the two are computed by the same cochain on the subgroup — so the localisations may
  be read at the level too, as maps of the quotient by the kernel to the quotients of the subgroups
  by their parts of it.  The hypothesis of the descent thereby becomes a statement about a group
  attached to the quotient alone: **the everywhere locally trivial classes of the first cohomology
  of the quotient with values in the first cohomology of the kernel**, which for a finite quotient
  is a group of ordinary group cohomology.
* `InverseGalois.CFT.Profinite.Discrete` says that last clause exactly.  On a discrete group the
  trivial subgroup is open, so every cochain is smooth and every action is smooth, and the smooth
  cocycles are all the cocycles; passing to classes, **the smooth cohomology of a discrete group is
  the ordinary cohomology of the additive copy of its coefficients**, in degree one and in degree
  two.  This is the seam between the two languages the development speaks.  Everything above a
  fixed finite level is written with smooth cochains on an infinite Galois group, because that is
  the language in which a class can be inflated from a level or restricted to a decomposition
  subgroup; everything below it is written with representations and complete cohomology, because
  that is the language of the theorems of Tate and Nakayama.  A class of the quotient crosses from
  one side to the other here and nowhere else.
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
* `InverseGalois.CFT.Profinite.H1Conj` puts the quotient back on what restriction produced.  An
  element of the ambient group conjugates a normal subgroup into itself, so substituting the
  conjugate and then acting on the coefficients carries a cochain on the subgroup to another one,
  and that substitution preserves the cocycle relation, the coboundaries and smoothness: **the
  ambient group acts on the first cohomology of a normal subgroup.**  Conjugating a cocycle by an
  element of the subgroup only multiplies it by the coboundary of the value the cocycle already
  takes there, so **the subgroup acts trivially and the action is one of the quotient**, smooth as
  soon as the subgroup is open.  This is the coefficient module the transgression of an
  inflation-restriction sequence asks for, and for the Galois group of a number field and the
  subgroup fixing a finite extension it is the module Kummer theory computes.
* `InverseGalois.CFT.Profinite.FixingSubgroup` reconciles the two pictures of that subgroup.  An
  automorphism of the extension fixing an intermediate field is an automorphism over that field,
  and Galois theory records this as an isomorphism of groups; but each side carries a topology of
  its own, the subgroup the one it inherits and the Galois group over the field the one built from
  the finite extensions of *that* field, and the two lattices of finite extensions are different.
  **The isomorphism respects both topologies.**  Enlarging a finite extension of the base by the
  intermediate field makes it finite over that field, which is one direction; the Krull topology of
  the big group already sees a finite extension of the intermediate field, which is the other.  So
  continuous cochains match up, and the first cohomology of the Galois group over an intermediate
  field *is* the first cohomology of the subgroup which fixes it — the transport is carried out for
  any isomorphism of topological groups smooth in both directions, since the argument sees only the
  substitution of one variable for another.
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
* `InverseGalois.CFT.PoitouTate.Dual` names the second factor that pairing wants.  The
  homomorphisms from a module to a fixed group of coefficients carry the action that transports the
  argument backwards and the value forwards, and this makes evaluation a pairing of a module with
  that Cartier dual, equivariant for the two actions and universal: sending an element to
  evaluation at it compares a module with its double dual.  An open normal subgroup acting
  trivially on the module and on the coefficients acts trivially on the homomorphisms between them,
  so **the Cartier dual of a smooth module is smooth**, and a module and its dual have cohomology
  of the same kind.
* `InverseGalois.CFT.PoitouTate.CupDual` cups along that evaluation.  A class with values in a
  module pairs with a class with values in its Cartier dual into a second cohomology class with
  values in the coefficients; the pairing commutes with restriction, so **either factor dying
  everywhere locally makes the product everywhere locally trivial**.  Over a number field the
  coefficients embed equivariantly in the units of a Galois extension, where the second cohomology
  is the Brauer group, so **the local invariants of the pairing of a class with a dual class
  multiply to one over all places** — a product formula of which the one for the power residue
  symbol is the case where the module and its dual are both the roots of unity.
* `InverseGalois.CFT.PoitouTate.ShaTate` reads the everywhere locally trivial classes as characters
  of complete cohomology.  A class of the first cohomology dying on every decomposition subgroup is
  inflated from the finite Galois level trivialising the coefficients, and inflation from a level
  is injective; on a finite group with the discrete topology smoothness is no condition, so the
  cohomology of the level is the ordinary cohomology of the additive copy of the coefficients,
  which is complete cohomology in degree one.  Thus **the everywhere locally trivial classes sit
  inside the complete cohomology of the level.**  When the coefficients are the maps of a finite
  module into a finite cyclic one killing it, that complete cohomology is dual to complete
  cohomology in degree minus two of the maps the other way and the rational circle is injective, so
  **every character of the everywhere locally trivial classes is the pairing against a single class
  in degree minus two.**
* `InverseGalois.CFT.PoitouTate.ShaSurjection` turns that exhaustion around.  Global duality for a
  finite module over a number field compares the everywhere locally trivial classes of the second
  cohomology with the characters of the everywhere locally trivial classes of the first cohomology
  of the Cartier dual; the two groups are cut out by the same local conditions, one degree apart
  and on coefficients traded for their dual.  Granted that comparison, a locally trivial class of
  degree two is a character, and every character comes from a single class of complete cohomology
  of the level, so **the complete cohomology of the level in degree minus two covers the everywhere
  locally trivial classes of the second cohomology** — the obstruction to an embedding problem
  which the local conditions have already killed everywhere locally becomes one class of a finite
  group's complete cohomology.
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
* `InverseGalois.CFT.Profinite.KummerHom` assembles those cocycles.  Two roots of the same unit
  differ by a root of unity of the base, which every automorphism fixes, so the coboundary of a
  root does not depend on the root, and a cocycle is determined by its coboundary because the
  coefficients inject into the units of the extension; choosing a root of every unit of the base
  therefore gives a homomorphism, multiplicative because a product of roots is a root of the
  product.  Its kernel is the powers and it is surjective, so **the units of the base modulo the
  `n`-th powers are the first cohomology with coefficients in the `n`-th roots of unity.**  The
  situation is not vacuous: over an algebraically closed extension the roots of unity of the base,
  with the trivial action, are such data.
* `InverseGalois.CFT.Profinite.KummerConj` lets a larger group watch.  Read Kummer theory over an
  intermediate field, normal over a smaller base, on the subgroup of the big Galois group which
  fixes that field: the classes of its units live in the first cohomology of a normal subgroup, and
  the base group acts on both sides, on units by restricting an automorphism and on cohomology by
  conjugating a cocycle.  **The two actions agree.**  The reason is that the Kummer cochain is
  characterised and not merely constructed, as the only cochain whose image is the coboundary of an
  `n`-th root: conjugating the cochain of a unit is the cochain built from the conjugate of the
  chosen root, which is a root of the conjugated unit, so the two agree before any class is taken.
  The one arithmetic input is that the roots of unity already lie in the small base, which is what
  makes an automorphism over it leave the coefficients alone.  Transporting the Kummer isomorphism
  itself across the two topologies then puts **the units of the intermediate field modulo `n`-th
  powers on the first cohomology of the subgroup**, an isomorphism of modules over the quotient.
* `InverseGalois.CFT.Profinite.KummerRes` restricts those classes.  The cochain of a unit measures
  how far a chosen root is from being fixed, and on a subgroup it is a coboundary exactly when it
  vanishes there, so **a Kummer class dies on a subgroup exactly when the unit is a power in the
  field that subgroup fixes**; one root is fixed precisely when every root is, because two roots
  differ by a root of unity of the base.  Over a family of subgroups this describes the everywhere
  locally trivial classes as the image of the units that are locally powers.
* `InverseGalois.CFT.Profinite.KummerTwo` runs the same computation one degree up.  A smooth
  cochain with values in the units is constant on the cosets of a finite level, so it has finitely
  many values and one open normal subgroup fixes them all, which makes its coboundary smooth.  If
  the image of a two cocycle is that coboundary, then the `n`-th power of the cochain has trivial
  coboundary, hence is a one cocycle, hence is the coboundary of a single unit by Hilbert's theorem
  ninety, and an `n`-th root of that unit corrects the cochain into one with values in the roots of
  unity: **the second cohomology with coefficients in the `n`-th roots of unity injects into the
  second cohomology of the units of the extension.**  Running the correction backwards, from a
  chosen root of every value of a cochain whose coboundary is the `n`-th power of a cocycle,
  identifies **the image as exactly the classes killed by `n`.**
* `InverseGalois.CFT.Profinite.Pi` takes the coefficients apart.  A cochain with values in a finite
  product is a family of cochains, one for each factor, and it is smooth exactly when each member
  is, being constant on the intersection of the finitely many levels the members need; the same
  reading of the cocycle condition and of the coboundaries gives **the first cohomology with
  coefficients in a finite product as the product of the first cohomologies**, the isomorphism
  being the family of the maps induced by the projections.  An isomorphism of the coefficients
  likewise induces one in cohomology, so a chosen decomposition of the coefficients turns a class
  into a family of classes.  Underneath both is the plainest fact about the construction: a
  coefficient map acts on cochains by composition, so **the passage to cohomology respects
  composition, the identity and — the coefficients being abelian — pointwise multiplication of
  coefficient maps**, and therefore carries a power of the identity to that power of the class.
* `InverseGalois.CFT.Profinite.PiTwo` reads the second cohomology of a product the same way.  The
  cocycle identity is an equation between values, so it holds in a product exactly when it holds in
  every factor, and for a finite family smoothness is again smoothness factor by factor; where the
  finiteness is spent a second time is injectivity, because a class dying in every factor is a
  family of coboundaries and the one cochains they come from have to be assembled into a single
  smooth one cochain.  So **the second cohomology of a finite product of coefficients is the
  product of the second cohomologies**, and transport along an isomorphism of the coefficients
  again carries a class to a family of classes.  Restriction to a subgroup commutes with a map of
  the coefficients — both are composition of the cocycle with something — so **a map of the
  coefficients preserves being everywhere locally trivial**.
* `InverseGalois.CFT.Profinite.Twist` puts the coefficients back together, and is the shape in
  which Kummer theory reaches a lifting problem.  The coefficients of such a problem are a finite
  module killed by a prime, which as an abstract group is a product of copies of the roots of
  unity, and a homomorphism of the roots of unity into it carries a Kummer class to a class with
  those coefficients, multiplicatively in the element of the base group and in the homomorphism.
  So the construction is a map out of the tensor product of the two, and **that map is an
  isomorphism onto the first cohomology with the larger coefficients.**  The inverse is a
  coordinate computation.  Each coordinate of a class comes from an element of the base group, well
  defined up to a `p`-th power — and a `p`-th power dies in the tensor product, the group of
  homomorphisms being killed by `p`.  That this is an inverse on one side is the observation that
  the coordinates of the class attached to the inclusion of a factor are the given class in that
  place and trivial elsewhere; on the other it is the observation that an endomorphism of a cyclic
  group is a power map, so each coordinate of a twisted class is a power of the class one started
  from, and those powers reassemble the homomorphism one started from.
* `InverseGalois.CFT.Profinite.TwistConj` makes the twist equivariant.  The first cohomology of a
  normal subgroup carries the conjugation action of the ambient group, and for a map of the
  coefficients to commute with it the map has to move as well: an element of the ambient group
  carries a homomorphism between two of its modules to the one which translates the argument
  backwards and the value forwards, and **that is an action of the ambient group on the
  homomorphisms of the coefficients** for which the induced map in cohomology is equivariant.  So
  **conjugating a twisted class is twisting by the conjugated element and the conjugated
  homomorphism**, once the classes the base group provides are themselves equivariant.
* `InverseGalois.CFT.Profinite.TwistTensor` says the same thing about the whole tensor product.  The
  twist is bilinear, so it is a map out of a tensor product, and conjugation moves the two factors
  separately — the classes the base group provides by whatever action they carry, the homomorphisms
  of the coefficients by conjugation.  **The twisting map out of the tensor product intertwines the
  two**, which is what makes the identification an identification of modules rather than of groups;
  a tensor product is generated by its pure tensors and both sides are additive, so there is nothing
  more to it.  For the action to be an action of the quotient the normal subgroup has to move both
  factors trivially, and on the homomorphisms of the coefficients that is automatic: **a subgroup
  acting trivially on the source and on the target acts trivially on the homomorphisms between
  them.**
* `InverseGalois.CFT.Profinite.TwistAction` turns that equivariance into a module structure.  **An
  element of a group acts on a tensor product of two of its modules by acting on each factor**, the
  diagonal action; a tensor product is generated by its pure tensors, so the axioms reduce to the
  axioms on each factor.  With the action in place the equivariance of the twisting map is an
  equation between an action and conjugation rather than between two tensor maps, which is the form
  the descent to the quotient consumes: **a subgroup acting trivially on both factors acts trivially
  on the tensor product**, and it acts trivially on the first cohomology of itself, so the two sides
  descend together.
* `InverseGalois.CFT.Profinite.KummerTwist` reads the two together over a field.  The Kummer
  homomorphism of an intermediate field is surjective with the `p`-th powers as its kernel, so it
  is exactly the datum the twist consumes: **the first cohomology of the subgroup fixing the field,
  with coefficients in a finite module killed by `p` which is a product of copies of the roots of
  unity, is the tensor product of the units of the field with the homomorphisms of the roots of
  unity into those coefficients**, and the Galois group of the base acts on the three sides
  compatibly — on the units by restriction, on the homomorphisms by translation of the value, on
  the cohomology by conjugation.  This is the shape in which the kernel of a lifting problem meets
  the units of the field the problem is solved over.  The equivariance is recorded on the whole
  tensor product as well, and **the subgroup fixing the field moves neither factor** — it restricts
  to the identity on the field, so it fixes the units, and it acts trivially on the roots of unity
  and on the coefficients, so it fixes the homomorphisms between them — which is what makes the
  identification one of modules over the Galois group of the finite extension.
* `InverseGalois.CFT.Profinite.KummerAction` takes that last step.  **The Galois group of the base
  acts on the units of a normal subextension by restriction**; the subgroup fixing the subextension
  restricts to the identity there, so it fixes the units, and it fixes the homomorphisms of the
  roots of unity into the coefficients, hence the tensor product of the two; and it acts trivially
  on the first cohomology of itself.  The quotient by it therefore acts on both sides and **the
  twisted Kummer identification is equivariant for that quotient** — which is the Galois group of
  the subextension, a finite group with no profinite group left in it.  This is the shape in which
  the locally trivial part of an obstruction is finally measured.
* `InverseGalois.CFT.Profinite.TwistRes` localises a twisted class.  A homomorphism of base groups
  induces a map of first cohomologies by precomposing a cocycle with it, a homomorphism of the
  coefficients induces one by postcomposing, and **the two compositions commute on the nose**.  So
  the twist is natural in the base group: once the classes the base group provides are carried to
  the classes its image provides, **the whole twisting map is carried to the twisting map of the
  image, tensored with the identity on the homomorphisms of the coefficients.**  Two cases are
  recorded, the restriction along an inclusion of subgroups and the restriction of the first
  cohomology of a normal subgroup to the part of it lying inside another subgroup — which read on
  the Galois group of a number field is the localisation of a class at a place.
* `InverseGalois.CFT.Profinite.KummerTower` carries Kummer theory up a tower of fields.  A unit of
  an intermediate field is a unit of every larger one, the subgroup fixing the larger field sits
  inside the subgroup fixing the smaller one, and **the restriction of the Kummer class of a unit is
  the Kummer class of that same unit read upstairs.**  The reason is once more that the Kummer
  cochain is characterised and not merely constructed: the root chosen upstairs and the root chosen
  downstairs are two roots of the same element of the ambient extension, so they have the same
  coboundary and the two cochains agree before any class is taken.  Twisting being natural in the
  base group, the same then holds for the coefficients of a lifting problem: read through the
  identification of the first cohomology with the tensor product of the units with the
  homomorphisms of the roots of unity, **restricting a class is including the units.**
* `InverseGalois.CFT.Profinite.KummerLocal` says which tower that is at a place.  A place is a
  decomposition subgroup, and localising a class of the subgroup fixing a subextension means
  restricting it to the part of that subgroup lying inside the decomposition subgroup.  **That part
  is the subgroup fixing the compositum of the subextension with the fixed field of the place**:
  the part of a subgroup inside another one and the intersection of the two have the same elements
  and the same topology, both inherited from the big group, so they induce the same map in the
  first cohomology; the subgroup fixing a compositum is the intersection of the subgroups fixing
  the factors; and a closed subgroup is the subgroup fixing its own fixed field.  Hence
  **localising a Kummer class at a place is including the units of the field into the units of that
  compositum**, and the same for the twisted identification.  The fixed field of a decomposition
  subgroup is an infinite extension of the base, which is why the tower below asks nothing of the
  size of the intermediate field.
* `InverseGalois.CFT.Profinite.KummerLocalSurjective` reads that identification in both directions.
  The comparison between the two readings of the part of a subgroup lying inside another one comes
  from an isomorphism of topological groups, so writing down the induced map of the inverse gives a
  two sided inverse and **the comparison is bijective**.  Transporting that bijectivity across the
  twisted Kummer identification turns two properties of the inclusion of the units into properties
  of localisation: **a twisted class dies at the place exactly when its datum dies under the
  inclusion**, **localisation is surjective as soon as the inclusion is surjective modulo the
  coefficients**, and consequently **whatever localisation kills is killed by every homomorphism
  that kills the classes whose datum the inclusion kills.**  This is what lets the compositum
  reading of a local condition be compared with any other reading of it.
* `InverseGalois.CFT.Profinite.KummerLocalCompare` performs that comparison.  Localisation at a
  place is a map of the coefficients of the first cohomology of the decomposition subgroup, and a
  surjective map of the coefficients kills the least a map can, so **a class trivial after
  localisation at the compositum is trivial after every map of the coefficients which kills the
  twisted Kummer data that the inclusion of the units kills** — and the same for a global class,
  restricted to the place first.  The map to be compared with is the one to the units of the
  completion of the level at the place below, for which the hypothesis to be checked is precisely
  that a unit which becomes a power in the compositum becomes a power in the completion.
* `InverseGalois.CFT.Profinite.KummerLocalQuot` moves that comparison to the level at which the
  obstruction reads it.  The coefficients of these classes are acted on through the quotient by the
  subgroup fixing the level, so a locally trivial class is already a statement about the finite
  quotient of a decomposition subgroup by its part fixing that level, and the comparison costs
  nothing to rewrite there: surjectivity of localisation and the description of what it kills are
  statements about the coefficients alone.  Hence **a class of that quotient trivial after
  localisation at the compositum is trivial after every map of the coefficients which kills the
  twisted Kummer data the inclusion of the units kills**, and **a class which is locally trivial at
  every subgroup of a family is killed at each member of that family.**
* `InverseGalois.CFT.Profinite.KummerRep` hands the identification over to class field theory.  An
  equivariant identification of an additive module with the additive copy of a multiplicative one is
  an isomorphism of representations over the integers, so **the twisted Kummer identification is an
  isomorphism in the category of representations of the quotient by the subgroup fixing the
  subextension**, and the two sides have the same cohomology.  Since that quotient is discrete, its
  smooth first cohomology is the ordinary first cohomology of the additive copy of its coefficients,
  and composing the two gives **the first cohomology of the Galois group of the subextension with
  values in the first cohomology of the subgroup as the first cohomology of that same finite group
  with coefficients in the units of the subextension tensored with the homomorphisms of the roots of
  unity.**  The everywhere locally trivial classes travel along it, and the two readings of them
  vanish together — which is what a local-global principle has to supply.
* `InverseGalois.CFT.Profinite.KummerFinite` names the group class field theory computes with.  The
  quotient of an infinite Galois group by the subgroup fixing a normal intermediate field is the
  Galois group of that field, restriction to it being surjective with that subgroup as kernel, and
  **the cohomology of a representation does not notice which of the two presentations of the group
  is used**: an identification of a module with the coefficients of a representation, equivariant
  along an isomorphism of the acting groups, is an isomorphism of representations once one of them
  is restricted along that isomorphism.  Composing with the identification above, **the first
  cohomology of the quotient with values in the first cohomology of the subgroup is the first
  cohomology of the Galois group of the intermediate field with coefficients in any representation
  identified with the units of that field tensored with the homomorphisms of the roots of unity into
  the kernel of a lifting problem** — for instance the tensor product of the representation on the
  units with a representation of the coefficients, which is the object the theorems of Tate and of
  Nakayama are stated about.  The everywhere locally trivial classes travel along it and the two
  readings of them vanish together.
* `InverseGalois.CFT.Profinite.KummerTransport` writes that identification on cocycles.  Both of the
  transports it is assembled from — the one along the identification of the coefficients and the one
  along the isomorphism of the acting groups — are the map induced by a homomorphism of the acting
  groups together with a map of the representations, in the forward direction, so **the class of a
  smooth one cocycle with values in the units is the class of the one cocycle read at the inverse
  isomorphism of the groups with its values carried across the identification of the
  coefficients.**  That is what makes the identification usable: restriction to a subgroup reads a
  cocycle at the elements of the subgroup and a map of representations applies to its values, while
  on the smooth side composition with a homomorphism of the acting groups and with a map of the
  coefficients does the same thing, so when the two homomorphisms agree and the two identifications
  of the coefficients agree the two cocycles are equal.  Hence **a smooth class whose localisation
  at a subgroup is trivial has vanishing image in the complete cohomology of that subgroup.**
* `InverseGalois.CFT.Profinite.KummerLocalTate` runs that argument on an everywhere locally trivial
  class.  All the local data are one additive map from the twisted Kummer coefficients to the
  coefficients of a representation of a decomposition subgroup, asked to kill what the inclusion of
  the units into the units of a compositum kills, to be equivariant, and to agree with the map of
  representations; everything else is bookkeeping, because a representation pulled back along an
  isomorphism of groups supplies the action localisation needs and the two readings of its
  coefficients are the identity.  Comparison with the compositum then kills the localised class at
  the level of the quotient, and the transport carries the vanishing across: **an everywhere locally
  trivial class, read over the Galois group of the level, dies under restriction to a decomposition
  subgroup followed by any map of representations induced by such a local map.**
* `InverseGalois.CFT.Profinite.Symbol` pairs two units of the base.  Cupping their Kummer classes
  along a pairing of the roots of unity with themselves gives **the `n`-th power symbol**, a
  bimultiplicative map on the units of the base with values in the second cohomology; it is killed
  by `n`, it is trivial as soon as one of its arguments is a power, and it commutes with
  restriction, so **it is everywhere locally trivial as soon as one of its arguments is everywhere
  a local power.**  The pairing of the roots of unity is a choice of a primitive root, which the
  integers modulo `n` carry for free: multiplication there is a pairing, and raising a chosen
  primitive root to a residue exhibits them as Kummer coefficients.  Composing with the inclusion
  of the roots of unity into the units of the extension lands the symbol in the second cohomology
  of the units, injectively when the extension is closed under `n`-th roots.
* `InverseGalois.CFT.Profinite.SymbolCyclic` rewrites that symbol in the shape a crossed product
  wants.  The Kummer cochain of a unit is a homomorphism to the residues modulo `n`, so a chosen
  `n`-th root of the unit is multiplied by a power of the fixed primitive root when an automorphism
  moves it; the powers of that root indexed by the second argument therefore have as coboundary the
  cup product times the two cocycle which records the carry, taking the value one when two residues
  add without wrapping around and the first argument when they wrap.  Hence **the power symbol is
  the inverse of the class of the carry cocycle of its arguments**, which is the cocycle of a
  cyclic algebra.
* `InverseGalois.CFT.Brauer.SymbolCyclicAlgebra` reads that off in the Brauer group.  The carry
  cocycle depends only on the Kummer character of the second argument, so a finite cyclic Galois
  level whose discrete logarithm to a chosen generator computes that character inflates its cyclic
  algebra cocycle exactly to the carry cocycle; the class is therefore computed at the level, and
  **the Brauer class of the power symbol is the inverse of the class of the cyclic algebra of its
  first argument.**  A cyclic algebra splits exactly when its unit is a norm, so **the power symbol
  is trivial exactly when its first argument is a norm from that level.**
* `InverseGalois.CFT.Profinite.KummerLevel` builds that level out of the unit alone.  An
  automorphism multiplies a chosen root of a unit by the power of the fixed primitive root recorded
  by the Kummer character, so it fixes the root exactly when the character vanishes on it and in
  any case carries the root into the field the root generates: **the field generated by a root of a
  unit is a finite Galois extension of the base**, and **the subgroup fixing it is the kernel of the
  Kummer character.**  Two automorphisms therefore restrict to the same automorphism of that field
  exactly when the character agrees on them, so if the character takes the value one somewhere, the
  restriction of such an automorphism generates: **a unit whose Kummer character is onto the
  residues modulo `n` generates a cyclic extension of degree `n` whose discrete logarithm computes
  the character.**
* `InverseGalois.CFT.Profinite.KummerLevelDegree` removes that hypothesis on the unit.  Agreeing on
  the character is the same as agreeing on the level, so the character descends to an injective
  homomorphism on the Galois group of the level and **the degree `m` of the level of a unit divides
  `n`.**  Each of the `m` values of the descended character is killed by `m`, hence a multiple of
  the index `t = n / m`, and there are exactly `m` such multiples, so the values are all of them and
  one automorphism has character exactly `t`.  That automorphism generates, and **the Kummer
  character of any unit is the discrete logarithm to a suitable generator of its level, scaled by
  the index** -- whence the carry condition of the character is the carry condition of the discrete
  logarithm, for every unit.
* `InverseGalois.CFT.Brauer.SymbolNorm` combines the two: **the power symbol of two units is trivial
  exactly when the first is a norm from the level of the second**, with nothing asked of either
  unit.  The level of a unit is generated by the chosen root, and the degree `m` of the level kills
  the character, so the `m`-th power of the root is fixed by the whole group and already lies in the
  base, say at `c`; the minimal polynomial of the root is then `X ^ m - C c` and its constant
  coefficient computes **the norm of the root as `c` up to the sign of `m`**.  Raising to the index
  `t` turns `c` into the unit itself, and the leftover sign is corrected by the norm of
  `ζ ^ (t / 2)` when `t` is even, since the resulting power of `ζ` is the one of order two.  So
  **every unit is, after the sign `(-1) ^ (n + 1)`, a norm from its own level** and the symbol of
  that corrected unit against the unit is trivial; applying this to a product and expanding by
  bilinearity leaves exactly the two cross terms, so **the power symbol is skew symmetric.**
* `InverseGalois.CFT.Brauer.SymbolSteinberg` computes the remaining universal relation.  The
  characteristic polynomial of multiplication by the chosen root is its minimal polynomial, so
  **the norm of a base element minus the root is that minimal polynomial evaluated at the base
  element**; one minus `e` times the root therefore has norm `1 - e ^ m * c`.  Taking for `e` the
  powers `ζ ^ j` with `j < t` makes those base values the roots of `X ^ t - C b`, whose value at
  one is `1 - b`, so multiplying the corresponding elements together shows **one minus a unit is a
  norm from the level of that unit** and hence **the power symbol of one minus a unit against that
  unit is trivial.**  Skew symmetry turns the arguments around, and writing the negative of a unit
  as the ratio of one minus the unit and one minus its inverse gives **the power symbol of a unit
  against its negative is trivial.**
* `InverseGalois.CFT.Units.KummerDecomposition` reads that off over a number field.  A cocycle for
  a trivial action is a homomorphism, and a homomorphism killing a level and every decomposition
  subgroup is trivial, so the first cohomology with roots of unity as coefficients has no
  everywhere locally trivial class; under the Kummer isomorphism, **a unit of a number field with a
  primitive root of unity which becomes a power in the decomposition field at every nonzero prime
  is already a power.**
* `InverseGalois.CFT.Profinite.ShaComap` moves local triviality along a homomorphism.  A continuous
  homomorphism carrying a subgroup of the source into a subgroup of the target makes the square
  formed by the two restrictions commute on the nose, both composites reading a cocycle on the
  images, so **a class dying on every subgroup of a family pulls back to a class dying on every
  subgroup of a family carried into it.**
* `InverseGalois.CFT.Units.DecompositionRestrict` applies that to a subfield.  A finite
  subextension of the base is generated by a finite set, so adjoining it to an intermediate field
  gives a finite subextension there and **restriction of scalars of an automorphism is continuous**;
  a prime of the ring of integers and an archimedean place are the same objects over either base,
  so **a decomposition subgroup over the intermediate field sits inside one over the base.**  Hence
  an everywhere locally trivial class of the second cohomology with roots of unity coefficients
  **dies as soon as one passes to a field containing a primitive root of unity.**  A finite module
  on which the group over the intermediate field acts trivially, and which is killed by the order
  of the roots of unity, is a product of copies of them; reading the class factor by factor gives
  the same conclusion there, so **an everywhere locally trivial class with coefficients in a
  finite module split by the intermediate field dies over that field.**
* `InverseGalois.CFT.Brauer.CyclicNormResidue` composes the invariant of a local field with the
  cyclic algebra construction: **the norm residue symbol of a cyclic extension of a local field.**
  The norm index of such an extension is the degree, whatever the ramification, so **its relative
  Brauer group has as many elements as the degree** and, being contained in the classes killed by
  the degree and as numerous as they are, **is exactly the classes killed by the degree.**  The
  invariant of a local field is injective, so **the symbol of a unit vanishes exactly when the unit
  is a norm**, and since the classes killed by the degree are all split by the extension, **the
  symbol attains the reciprocal of the degree.**  None of this asks the extension to be unramified.
* `InverseGalois.CFT.Brauer.LocalReciprocityAll` removes the last hypothesis from the count.  The
  base-change formula for the invariant map asks the extension to carry an absolute value
  restricting to the one below, and a finite extension of a local field carries the value of the
  field norm, which restricts to the degree-th power of the value below; but a comparison map of a
  rank one valuation may be composed with the degree-th root, which is again strictly monotone,
  kills zero, fixes one and preserves products, so it is again a comparison map, and the absolute
  value it defines does restrict to the one below.  A generator of the value group of either sign
  serves, since the opposite of a generator is again one.  None of the data chosen appears in the
  conclusion, so it may all be chosen inside the proof: **the relative Brauer group of an arbitrary
  finite Galois extension of a local field is exactly the classes killed by the degree, and has as
  many elements as the degree** — with no hypothesis on the ramification, on the Galois group, or
  on the absolute value of the extension.  The same construction, applied to an intermediate field
  rather than to the whole extension, says that **a finite extension of a local field is again a
  local field** and so carries local reciprocity itself: the count holds for a finite Galois
  extension of any intermediate field of a finite extension of a local field.
* `InverseGalois.CFT.Units.CompletionCyclic` supplies the group theory that makes the local theory
  of a cyclic extension apply at a place of a global one.  An automorphism of a completion is
  continuous and the field is dense in it, so **restriction to the field is injective on the Galois
  group of the completion**; hence **the completion of a cyclic extension of number fields is a
  cyclic extension of the completion below.**
* `InverseGalois.CFT.Brauer.RelativeHasse` reads the Albert-Brauer-Hasse-Noether theorem as a
  statement about a fixed extension rather than a fixed class.  Base change is functorial, so the
  completion of the base-changed class at a place of the extension is the base change of the class
  to that completion, and **a Brauer class of a number field is split by a finite extension exactly
  when every completion of the extension splits it.**  A complex place of the extension is the
  complex numbers over the base and splits everything, so only the finite places and the real
  places appear, and **at a finite place the condition is one over the completion of the base.**
* `InverseGalois.CFT.Brauer.RelativeCyclic` combines the two with the local theory.  At a finite
  place the completion of a cyclic extension is a cyclic extension of the completion below, whose
  relative Brauer group is the classes killed by its degree, so **that place splits a class exactly
  when the local degree kills the invariant at the place below**; hence **a cyclic extension of
  number fields splits a Brauer class exactly when every local degree kills the invariant at the
  place below and every real place of the extension splits the class.**
* `InverseGalois.CFT.Local.GaussNorm` recognises an unramified extension from a single polynomial.
  Writing an element of an extension generated by one element in the power basis, the largest
  absolute value of a coordinate is an absolute value: multiplicativity is the only point, and it
  holds because the product of two representatives, reduced modulo a monic minimal polynomial with
  integral coefficients, keeps a coefficient of absolute value one as soon as the reduction of that
  minimal polynomial is irreducible over the residue field, the quotient by it being a field.  By
  the uniqueness of the extension of a complete nonarchimedean absolute value this **Gauss norm is
  the spectral norm**, so every value it takes is already the absolute value of a scalar and
  therefore **a generator whose minimal polynomial stays irreducible modulo the maximal ideal
  generates an unramified extension of local fields.**
* `InverseGalois.CFT.Local.KummerIrreducible` removes the parity restriction from the criterion for
  a radical polynomial to be irreducible.  Splitting a prime factor off the exponent, the norm of a
  root of the radical of the complementary exponent is a power of the constant term up to the sign
  of the parity of that factor, and over a field with a square root of minus one an opposite is a
  power exactly when the element is; so **the difference of a power of the variable and a constant
  is irreducible as soon as the constant is not a power of any prime order dividing the exponent**,
  for every nonzero exponent whose multiples of four come with a square root of minus one.
* `InverseGalois.CFT.Local.RadicalUnramified` applies that criterion to a radical extension.  A unit
  which becomes a power of an exponent prime to the residue characteristic modulo the maximal ideal
  is already a power, because a unit congruent to one is a power with that exponent; so for a prime
  exponent the reduction of the difference of that power of the variable and the unit stays
  irreducible and **adjoining a root of prime order of a unit gives an unramified extension.**  The
  norm subgroup of a cyclic extension of a local field has index the degree and the invariant of an
  unramified extension reads the value, which is trivial on a unit, so **every unit of the valuation
  ring of the base is a norm from such an extension.**
* `InverseGalois.CFT.Brauer.LocalSymbolUnits` reads that as a relation for the symbol.  The level of
  a unit for a prime exponent has degree one or the exponent, and in either case a unit of the
  valuation ring is a norm from it, so **the norm residue symbol of two units of the valuation ring
  is trivial** whenever the residue characteristic does not divide the prime exponent.  The
  invariant map being an isomorphism, skew symmetry, the Steinberg relation and the triviality of
  the symbol of a unit against its negative also descend from the power symbol, so **a tame symbol
  is determined by the values of its two arguments.**
* `InverseGalois.CFT.Brauer.TameSymbol` carries that out.  Choosing a uniformiser writes every
  element as a power of it times a unit of the valuation ring, and bilinearity together with skew
  symmetry, the triviality of the symbol of a uniformiser against its own negative and the
  triviality of the symbol of two units move every occurrence of the uniformiser into the first
  argument, so **the symbol of two elements is the symbol of the uniformiser against an explicit
  unit of the valuation ring** built from the two elements and their values.  A unit congruent to
  one is a power of any exponent prime to the residue characteristic, so **that remaining pairing
  only sees the residue of its second argument.**
* `InverseGalois.CFT.Brauer.TameEvaluation` evaluates what is left.  A subgroup of the units of the
  base which contains every unit of the valuation ring and a uniformiser is everything, because
  dividing by the matching power of the uniformiser leaves a unit of the valuation ring; the norm
  subgroup of the level of a unit contains every unit of the valuation ring and has index the degree
  of that level, so **a uniformiser is a norm from the level of a unit exactly when that level is
  trivial**, which happens exactly when the unit is a power.  Together with the tame form this is
  **the kernel of the norm residue symbol**: the symbol of two elements is trivial exactly when the
  unit of the valuation ring built from them and their values is a power, and the symbol of a
  uniformiser against a unit of the valuation ring which is not a power **has order the exponent.**
* `InverseGalois.CFT.Brauer.TameValue` computes the value itself.  The level of a unit of the
  valuation ring which is not a power of prime order is the radical extension by that unit, and the
  reduction of the minimal polynomial of the chosen root stays irreducible, so **that level is
  unramified**; the symbol of a uniformiser against the unit is therefore the inverse of the class
  of a cyclic algebra over an unramified extension, whose invariant is the value of the uniformiser
  divided by the degree once the invariant is taken with respect to the generator matching the
  Kummer character.  Rescaling that generator to the Frobenius automorphism multiplies the invariant
  by the discrete logarithm of the Frobenius automorphism, which is the value of the Kummer
  character of the unit at any automorphism inducing it, so **the tame symbol of a uniformiser
  against a unit of the valuation ring is the class, modulo the integers, of the opposite of the
  Kummer character of that unit at a Frobenius automorphism, divided by the exponent.**
* `InverseGalois.CFT.Brauer.TameResidue` reads that value classically.  The chosen root of a unit
  of the valuation ring has absolute value one, and a Frobenius automorphism of its level both
  multiplies it by the root of unity the Kummer character names and moves it to within distance one
  of its power by the number of residues of the base, so cancelling the chosen root leaves that
  root of unity congruent to a power of it; the exponent divides one less than the number of
  residues, so that power is a power of the unit itself and no trace of the level survives.  Two
  roots of unity of order prime to the residue characteristic at distance less than one are equal,
  so **the Kummer character of a unit at a Frobenius automorphism is the power residue exponent of
  that unit**, and **the tame symbol of a uniformiser against a unit of the valuation ring is the
  class, modulo the integers, of the opposite of the power residue exponent of the unit, divided by
  the exponent.**
* `InverseGalois.CFT.Brauer.PlaceCyclic` moves the computation from a completion back to the number
  field it completes.  A cyclic extension has, above every finite place, a decomposition group
  generated by the power of the chosen generator by the number of places above it, so the
  completion of the extension is cyclic with such a generator; extending scalars to the completion
  factors through the decomposition field, and neither the restriction to that field nor the
  compositum with the completion touches the coefficient, so **the localization of a cyclic algebra
  at a finite place is the cyclic algebra of the decomposition group with the same coefficient**.
  Reading the local invariant of that algebra gives **the invariant at a finite place of a cyclic
  algebra as the invariant of its coefficient raised to the discrete logarithm of the Frobenius
  automorphism**, and in particular **a cyclic algebra whose coefficient is a unit at an unramified
  place has trivial invariant there**, so only the places dividing the coefficient and the ramified
  places can contribute to the sum of the invariants over all places.
* `InverseGalois.CFT.Brauer.PlaceUnramified` supplies the unramifiedness that computation asks for.
  Every automorphism of the completion comes from the decomposition group, which acts by isometries,
  so the norm of an element of the completion, being the product of its conjugates, has the value of
  that element raised to the degree; when the ramification index is one that value is already the
  value of a scalar, so **every absolute value of the completion at an unramified place is an
  absolute value of a scalar**.  The Galois group of the completions is finite, so a generator has
  the Frobenius automorphism among its powers, and therefore **a cyclic algebra whose coefficient is
  a unit at a finite place unramified in the extension has trivial invariant at that place**, with
  nothing left to supply.
* `InverseGalois.CFT.Brauer.PlaceFrobenius` describes that Frobenius automorphism on the roots of
  unity.  At a place of ramification index one the absolute value of the division algebra and the
  valuation of the completion answer the same two questions, because the value of the algebra norm
  is the degree-th power of the value; so an automorphism raising every residue of the division
  algebra to the power given by the number of residues of the base does the same for the valuation,
  and roots of unity of order invertible in the residue field are separated by the maximal ideal.
  Hence **the Frobenius of a completion raises a root of unity of order invertible in the residue
  field to the power given by the number of residues of the base**, which is the cyclotomic
  description of the Frobenius, obtained with no global Frobenius element in sight; and every
  automorphism of the completion restricts to the extension compatibly with the inclusion, so the
  same holds for **a root of unity of the extension itself**.
* `InverseGalois.CFT.Brauer.ResidueCard` names the exponent in that description.  The residues of a
  field are a finite ring without zero divisors, and every one of them is the residue of a rational
  integer as soon as every integer of the field is congruent to a rational integer; a rational
  integer is congruent to one of the residue characteristic many of them, while the residue of one
  already has that additive order.  So **a field whose integers are congruent to rational integers
  and whose residue characteristic is `p` has exactly `p` residues**, and since residue degree one
  is exactly the congruence in question, **the completion of a number field at a place of residue
  degree one over `p` has exactly `p` residues**.  Over the rationals every finite place has residue
  degree one, so the Frobenius of a completion of an extension of the rationals raises a root of
  unity to the power of the rational prime below the place.
* `InverseGalois.CFT.Local.RatResidueDegree` is the residue degree over the rationals.  A finite
  place lies over the rational prime it contains, because the ideal that prime generates is maximal
  and the ideal below the place is proper; and over the rationals the residue degree of a place is
  at most the degree of the field over the rationals and is positive, so **every finite place of the
  rationals has residue degree one**.  Hence **the completion of the rationals at a finite place has
  exactly as many residues as the rational prime the place contains**, and **over the rationals the
  Frobenius of an unramified place of a field generated by a root of unity is the automorphism
  raising that root of unity to the power of that prime** — the description of the Frobenius as an
  element of the Galois group, since two automorphisms agreeing on a generator are equal.
* `InverseGalois.CFT.Brauer.PlaceExponent` turns that element into the local invariant.  Restriction
  to the extension is a group homomorphism, and it identifies an automorphism of the completion with
  the automorphism it induces over the decomposition field, so **the Frobenius of a completion
  restricts to the power of a generator of the Galois group given by the index of the decomposition
  group times the local exponent**; and since **the index times the local degree is the degree**,
  the two ways of dividing agree modulo the integers.  Hence **the invariant at a finite place of a
  cyclic algebra is the exponent expressing the restricted Frobenius as a power of the chosen
  generator, times the value of the coefficient at the place, divided by the degree** — the local
  invariant computed from a global datum.
* `InverseGalois.CFT.Brauer.PlaceCyclotomic` removes the local data from that description: the
  generator of the Galois group of the completions and the exponent of the local Frobenius are both
  produced by the extension, so **at an unramified finite place the invariant is determined by the
  ramification index and the exponent of the restricted Frobenius**, and in particular **it is
  trivial wherever the coefficient is a unit**.  Over the rationals the restricted Frobenius is the
  automorphism raising a generating root of unity to the power of the prime below the place, and for
  a subfield of a cyclotomic field away from the conductor both remaining side conditions hold
  automatically.
* `InverseGalois.CFT.Brauer.RatCount` counts the places that contribute.  **The invariant of a
  cyclic algebra over the rationals vanishes at every finite place containing no prime of the
  conductor at which the coefficient is a unit**, and the product of the local invariants over the
  finite places is a finite product over any set outside which they vanish, so **for a totally real
  splitting field inside a cyclotomic field with a single ramified prime and a rational prime as
  coefficient the sum of all the local invariants has exactly two terms**.
* `InverseGalois.CFT.Brauer.CyclotomicFrobenius` names the automorphism that computes the surviving
  unramified term.  Through the description of the Galois group of a cyclotomic field as the units
  of the integers modulo the conductor, a natural number prime to the conductor names **the
  automorphism raising every root of unity of order dividing the conductor to that power**, and a
  chosen primitive root generates the field, so **the invariant of a cyclic algebra over the
  rationals at a place of a cyclotomic field away from the conductor is the exponent expressing that
  automorphism as a power of the chosen generator, times the value of the coefficient, divided by
  the degree**.
* `InverseGalois.CFT.Local.CyclotomicUniformiser` describes the ramified place.  A prime of odd
  order is the product of the partial geometric sums of a primitive root of unity of that order
  times the corresponding power of the difference of the root and one, and each partial sum is
  congruent to the number of its terms, so by Wilson's theorem **the power of exponent one less than
  the prime of the difference of the root and one is the opposite of the prime, times a factor
  congruent to one** — in particular **a primitive root of unity of prime order is congruent to
  one** in any valued field of that residue characteristic.
* `InverseGalois.CFT.Local.CyclotomicRadical` extracts the radical hidden at the ramified place.
  Correcting the difference of a primitive root of unity of prime order and one by a unit congruent
  to one produces **a root of the opposite of the prime of exponent one less than the prime**, and
  such a root is congruent to the difference itself.  An automorphism of the field is then pinned
  down on it by its effect on the root of unity: **an automorphism raising the root of unity to a
  power multiplies the radical by the root of unity of order one less than the prime whose residue
  is that power**.  Raising the radical to a power descends it to any exponent dividing one less
  than the prime, and the multiplier descends with it; a root of unity congruent to a natural number
  of that multiplicative order modulo the prime is primitive, so the descended multiplier is a
  primitive root of unity of the smaller exponent.  At the other extreme, a root of unity of order
  prime to the residue characteristic congruent to one is one, so **an automorphism whose power of
  the exponent is congruent to one modulo the prime fixes the descended radical outright**.
* `InverseGalois.CFT.Brauer.LocalSymbolRamified` computes the invariant of a cyclic algebra over a
  ramified level.  The power symbol of two units is the inverse of the class of the cyclic algebra
  of the first over any cyclic level carrying the Kummer character of the second, and the invariant
  map is defined on the whole Brauer group, so **the norm residue symbol of two units is the inverse
  of the invariant of that cyclic algebra**, with no unramifiedness hypothesis on the level.
* `InverseGalois.CFT.Brauer.CyclicTransport` moves a cyclic algebra between splitting fields.  **An
  isomorphism of two cyclic extensions of the base carrying one chosen generator of the Galois group
  to the other leaves the Brauer class of the cyclic algebra unchanged**, because the cyclic algebra
  of the first extension already contains a copy of the second in which the very same unit
  implements the second generator.
* `InverseGalois.CFT.Local.ResidueRootUnity` lifts the roots of unity of the residue field.
  Fermat's little theorem makes the power of exponent one less than the residue characteristic of a
  natural number prime to it congruent to one, and such a factor has a root of that exponent again
  congruent to one, so dividing the number by that root produces **a root of unity of order one less
  than the residue characteristic congruent to the number**.  Taking the number to be a primitive
  root modulo the residue characteristic and raising to the complementary power, **a complete valued
  field of residue characteristic `q` contains a primitive root of unity of every order dividing
  `q - 1`**.
* `InverseGalois.CFT.Brauer.TamePower` removes the last hypothesis from the tame symbol.  A unit
  which is an exact power has the power of its root by one less than the number of residues for its
  power residue value, hence a power residue exponent divisible by the exponent, and the symbol is
  trivial on a power as well, so **the tame norm residue symbol of a uniformiser against any unit of
  the valuation ring is the class, modulo the integers, of the opposite of the power residue
  exponent of the unit divided by the exponent**.  The symbol is multiplicative in the uniformiser,
  so for a uniformiser whose divided valuation is minus one — the normalisation an actual
  uniformiser of a completion carries — the sign is the other one, and the symbol is skew
  symmetric, so **the tame norm residue symbol of a unit against such a uniformiser** is read off
  the power residue exponent as well.
* `InverseGalois.CFT.Brauer.TameOdd` reads that symbol against an arbitrary exponent of an
  irreducible radical polynomial, an odd one in particular.  A unit whose power residue value is a
  primitive root of unity of the exponent is a power of no prime order dividing the exponent, for a
  root of that order would be a root of unity of a proper divisor of the exponent, so its symbol
  against a uniformiser is the class, modulo the integers, of the opposite of the inverse of the
  exponent.  Any unit congruent to a power of that one differs from that power by a unit congruent
  to one, which is an exact power, so **the tame norm residue symbol of a uniformiser against a unit
  congruent to a power of the chosen one is the class, modulo the integers, of the opposite of that
  power divided by the exponent**, and the two normalisations of the uniformiser and the two orders
  of the arguments give the three remaining signs.
* `InverseGalois.CFT.Local.RatUniformiser` supplies that local datum over the rationals.  The
  ramification index of a finite place of the rationals is at most the degree of the rationals over
  themselves and is positive, so **a finite place of the rationals is unramified over the rational
  prime below it**; the valuation of a rational prime is the exponential of minus that index, so
  **a rational prime is a uniformiser of the completion of the rationals at a place containing it**
  and **that completion has the prime as its residue characteristic, with exponent one**.  Dividing
  the valuation of a unit by the generator of the value group leaves the logarithm alone, so **the
  reciprocal of a uniformiser has divided valuation one**.
* `InverseGalois.CFT.Units.AdicRadical` puts the radical in the completion of a number field.  A
  primitive root of unity stays primitive there, so **the completion of a number field containing a
  primitive root of unity of odd prime order, at a place containing that prime, carries a radical of
  the opposite of the prime of every exponent dividing one less than it**, one and the same radical
  for every isometry of the completion.  The automorphisms of a decomposition group give such
  isometries, acting on the image of the field through the global automorphism they come from, and
  the base field plays no role in that description.  **An automorphism of finite order raises a root
  of unity to an exponent whose power of that order is congruent to one**, and over an intermediate
  field every automorphism has order dividing the number of automorphisms of the extension, so
  **the radical comes from the completion of the intermediate field**.
* `InverseGalois.CFT.Brauer.PlaceTotallyRamified` reads the local data at the place where that
  radical lives.  Inertia sits inside the decomposition group, so **the decomposition group of a
  totally ramified prime is the whole Galois group**; its index is then one, whence **the local
  degree at a totally ramified place is the degree of the extension** and **the Galois group of the
  completions has a generator restricting to a prescribed generator of the Galois group of the
  extension**, with no correcting power in between.  A finite place of the rationals is determined
  by the rational prime it contains, so **the place of the rationals below a place above a rational
  prime is the place attached to that prime**, and conversely.
* `InverseGalois.CFT.Local.ResiduePrimitiveRoot` names the residue the radical is to have.  The
  multiplicative group of the residues modulo a prime is cyclic, so **a prime has a primitive
  root**, and raising the root of unity above it to the complementary power, **a complete valued
  field of residue characteristic a prime contains, for every factorisation of one less than that
  prime, a primitive root of unity of the second factor congruent to the first power of a
  prescribed primitive root**.  Prescribing the residue is what makes the root of unity usable in a
  field and in an extension of it at once.
* `InverseGalois.CFT.Units.RadicalDescent` brings the radical and its multiplier down a tower.  The
  radical of a normal extension is fixed by the decomposition group over an intermediate field, so
  **the completion of the intermediate field carries a radical of the opposite of the prime of
  every exponent whose complementary factor is the degree of the upper layer**; an automorphism of
  the top field fixing the place acts on the smaller completion through its restriction, so the
  root of unity multiplying the radical descends with its order and its residue.  Two roots of
  unity of an order prime to the residue characteristic agreeing on residues are equal, whence
  **the automorphism of the intermediate completion multiplies the radical by a root of unity
  prescribed in the completion of the base**.
* `InverseGalois.CFT.Brauer.RadicalLevel` matches the radical presentation of a cyclic level with
  the Kummer presentation.  The radical and the chosen root of its power differ by a root of unity
  of the base, so an automorphism moves the two by the same root of unity, and **the discrete
  logarithm of a level presented by a radical computes the Kummer character of the power of the
  radical**.  That is the hypothesis under which the power residue symbol is the class of a cyclic
  algebra, so a level offered in radical form can be fed to the symbol directly.
* `InverseGalois.CFT.Brauer.RadicalInvariant` evaluates the invariant of a cyclic algebra whose
  level is given by a radical.  The carry condition is automatic there, and an abstract cyclic
  extension may be embedded into the algebraic closure without changing the Brauer class or the
  radical, so **the invariant of a cyclic algebra over a cyclic extension presented by a radical is
  the inverse of the power residue symbol of its coefficient against the power of the radical**.
  A totally ramified cyclic extension of a local field is presented that way, so this is what
  computes the invariant at a ramified place.
* `InverseGalois.CFT.Brauer.PlaceRadical` reads that computation globally.  Base change to the
  completion turns a cyclic algebra into the cyclic algebra of the decomposition group with the
  same coefficient, so **the invariant at a finite place of a cyclic algebra whose completed
  splitting field is presented by a radical is the inverse of the power residue symbol of its
  coefficient against the power of the radical**.  At a totally ramified place the local generator
  restricts to the global one, so no correcting power survives.
* `InverseGalois.CFT.Brauer.PlaceRamified` evaluates that symbol.  The power of the radical has the
  divided valuation of the inverse of a uniformiser, so the tame computation applies after a skew
  symmetry, and its sign cancels against the sign of the inverse: **the invariant at a totally
  ramified place of a cyclic algebra whose completed splitting field is presented by a radical, of
  a coefficient which is a unit of the valuation ring, is the class modulo the integers of the
  power residue exponent of the coefficient divided by the exponent**.
* `InverseGalois.CFT.Brauer.PlaceRamifiedAut` states that evaluation without any local Galois data.
  An automorphism of the completion is determined by its restriction to the extension, so it is the
  automorphism induced by that restriction, and the radical presenting the completion may therefore
  be moved by the automorphism induced by the chosen generator; the order of the Galois group of the
  completions at a totally ramified place is the degree of the extension, so **the invariant is
  prescribed by the extension, the chosen generator, and the power residue exponent alone**.
* `InverseGalois.CFT.Brauer.PlaceSubcyclotomic` brings the unramified term down to the subfield that
  actually splits the algebra.  The cyclic algebra of a subfield for the restricted generator is the
  cyclic algebra of the cyclotomic field for the coefficient raised to the relative degree, and that
  degree cancels between the value of the power and the degree of the cyclotomic field, so **the
  invariant of a cyclic algebra over the rationals split by a subfield of a cyclotomic field, at a
  place away from the conductor, is the exponent of the automorphism raising the roots of unity to
  the power of the prime below the place, times the value of the coefficient, divided by the degree
  of the subfield**.  A rational prime is a uniformiser of the completion at the place it
  determines, so **its value there is minus one** and for that coefficient only the exponent, with a
  sign, survives.
* `InverseGalois.CFT.Brauer.CyclotomicGenerator` identifies the exponent that appears there.  The
  Galois group of a cyclotomic field of prime conductor is the group of units of the residues, in
  which a primitive root has the order of the whole group, so **the automorphism raising the roots
  of unity to the power of a primitive root generates the Galois group** and every automorphism
  naming a number prime to the conductor is a natural power of it.  Reading that identity in the
  group of units, **the exponent expressing one such automorphism as a power of another expresses
  the first number as a power of the second modulo the conductor** — the discrete logarithm.
* `InverseGalois.CFT.Local.ResidueDiscreteLog` turns that discrete logarithm into the congruence the
  power residue symbol reads.  A multiple of the residue characteristic has valuation less than one,
  and congruences multiply, so **the power by the discrete logarithm of a root of unity congruent to
  a power of a primitive root is congruent to the same power of the number**.  The root of unity
  supplied by the residue prescription is exactly the one whose power the ramified invariant tests.
* `InverseGalois.CFT.Brauer.PlaceConductor` assembles the ramified term.  The conductor is totally
  ramified in a cyclotomic field of prime conductor, so the chosen generator fixes the place above
  it and the completion of the subfield is presented by a radical of the opposite of the conductor
  moved by the prescribed root of unity, whose coefficient is a uniformiser of the completion of the
  rationals; the congruence above supplies the power residue exponent.  Hence **the invariant at the
  place of the conductor of a cyclic algebra over the rationals split by a subfield of a cyclotomic
  field of prime conductor, of a rational prime away from the conductor as coefficient, is the
  discrete logarithm of that prime divided by the degree of the subfield**.
* `InverseGalois.CFT.RatUnits` records what is left to check once the primes away from the
  conductor are settled.  A nonzero rational is its numerator over its denominator and each of
  those is a signed product of primes, so **a multiplicative map out of the units of the rationals
  that kills minus one and every prime is trivial**.
* `InverseGalois.CFT.Cyclotomic.SubfieldNorm` disposes of the two coefficients the local
  computation does not reach.  Taking the norm in two steps factors the norm of a cyclotomic field
  through any intermediate field, and an odd prime is the norm of one less than a primitive root of
  unity of that conductor, so **an odd prime conductor is a norm from every intermediate field of
  its cyclotomic field**; and the norm of a scalar is its power by the degree, so **minus one is a
  norm from an extension of the rationals of odd degree**.
* `InverseGalois.CFT.Brauer.SubcyclotomicReciprocity` puts the two terms together.  They carry the
  same discrete logarithm with opposite signs, so **the sum of all the local invariants of a cyclic
  algebra over the rationals split by a totally real subfield of the cyclotomic field of an odd
  prime conductor, with a rational prime away from the conductor as coefficient, vanishes** — the
  reciprocity law for that family.  When the subfield has odd degree the conductor and minus
  one are norms from it, so the algebras they name are trivial; minus one and the rational primes
  generate the units of the rationals, and therefore **the sum of all the local invariants vanishes
  for every rational coefficient**.
* `InverseGalois.CFT.Brauer.OddArchimedean` starts the passage from that family to an arbitrary
  class of odd order.  The Brauer group of the reals has two elements, so a class killed by an odd
  exponent is killed both by two and by that exponent, hence **is split by the reals**, and by the
  completion of any number field at a real place; **the total invariant of such a class is
  therefore the product of its invariants at the finite places**, and the archimedean conditions of
  the Hasse principle are automatic.
* `InverseGalois.CFT.Brauer.OddArchimedeanBase` repeats that observation over an arbitrary number
  field.  The completion at a real place is the reals over the base, whose Brauer group is killed
  by two, and the completion at a complex place is algebraically closed, so **a Brauer class of a
  number field killed by an odd exponent has trivial invariant at every infinite place** and **its
  total invariant is the product of its invariants at the finite places**.
* `InverseGalois.CFT.Brauer.SplitLocalDegree` reads a completely split prime locally.  The order of
  the decomposition group at a prime is the ramification index times the residue degree and also
  the degree of the completion over the completion below, so **a rational prime splits completely
  exactly when its decomposition group is trivial** and **in a Galois extension of the rationals of
  prime degree that degree divides the local degree at a prime that does not split completely** —
  which is what makes such a field split a class whose local invariant is killed by the degree.
* `InverseGalois.CFT.Scholz.RadicalDegree` measures the enlargement a radical makes.  Over a field
  already containing the `ℓ`-th roots of unity the roots of one rational number differ by roots of
  unity, so **the compositum with the radical field of one number is generated by a single `ℓ`-th
  root of it**; for `ℓ` prime and the number without an `ℓ`-th root there that root has minimal
  polynomial `X ^ ℓ` minus the number, so **the compositum has degree exactly `ℓ` times the degree
  of the field**.
* `InverseGalois.CFT.Scholz.QuarticRadical` supplies the same measurement for fourth roots, which
  is what the prime two needs.  A rational number can acquire a square root in an abelian extension
  of the rationals, but not a fourth root: comparing the two automorphisms that negate a square
  root of the number and a square root of minus one shows that **an abelian extension contains no
  fourth root of a rational number `m` whenever `m`, `-m` and `-1` are all rational non-squares**.
  In the other direction, over a field containing a square root of minus one the norm of a square
  root of an adjoined square root would, corrected by that square root of minus one, be a square
  root of the constant, so **`X ^ 4` minus a non-square is irreducible there**.
* `InverseGalois.CFT.Scholz.DyadicAuxPrime` runs the density argument at the prime two, where
  squares are not enough: a prime congruent to one modulo a high power of two is congruent to one
  modulo eight, so two is always a square modulo it.  Raising the exponent repairs this.  Over the
  cyclotomic field of a two-power conductor at least four, only two is ramified, so an odd prime
  has no square root there and its fourth radical multiplies the degree by four, while the fourth
  radical of two at least doubles it because that field is abelian.  A quarter and a quarter, or a
  half and a quarter, fall short of one, so the density bound yields **a prime congruent to one
  modulo a prescribed power of two modulo which two prescribed primes, not both two, are
  simultaneously fourth-power non-residues**.
* `InverseGalois.CFT.Scholz.AuxPrimePair` spends that exact degree on two conditions at once.  Two
  reciprocals of `ℓ` times a degree fall short of the reciprocal of the degree once `ℓ` is at least
  three, so the density bound of `InverseGalois.NumberTheory.SplitDensityPair` leaves **infinitely
  many primes splitting completely in a Galois extension of the rationals but in neither of the
  radical fields of two prescribed numbers**, that is, **a prime modulo which two prescribed
  integers are simultaneously not `ℓ`-th power residues**.  Correcting one place at a time trades
  one bad place for another and never reduces their number; two at once is what makes the count
  drop.
* `InverseGalois.CFT.Cyclotomic.AuxiliarySubfield` assembles the field the reciprocity law wants.
  The units modulo a prime are cyclic, so **a natural number whose powers exhaust the nonzero
  residues modulo a prime** exists and names a generator of the Galois group; and inside the
  cyclotomic field of a prime conductor there is **a totally real subfield of any prescribed degree
  dividing half the degree**, totally ramified at that conductor, in which **a rational prime
  splits completely exactly when it is a power residue of the matching exponent**.
* `InverseGalois.CFT.Brauer.SubcyclotomicSplit` turns that splitting law into reciprocity for a
  class rather than for a coefficient.  At a place above a prime that does not split completely in
  an extension of prime degree the local degree is the whole degree, and the real places split a
  class of odd order, so **a class of odd prime order is split by a cyclic extension of that degree
  in which no prime carrying a nontrivial invariant splits completely**; a split class is a cyclic
  algebra, so **the total invariant of a class split by such a totally real subfield vanishes**,
  and therefore **reciprocity holds for a class of odd prime order all of whose bad primes are
  power non-residues modulo an auxiliary prime**.
* `InverseGalois.CFT.Brauer.SubcyclotomicCorrector` builds the class that moves an invariant.  A
  power non-residue is a power of a primitive root with exponent prime to the degree, and a residue
  class prime to a prime generates the elements killed by it, so a suitable power of the cyclic
  algebra of that prime gives **a class of odd prime order with trivial total invariant, a
  prescribed invariant at a given prime, and trivial invariants away from that prime and the
  auxiliary one**.
* `InverseGalois.CFT.Brauer.RatReciprocity` runs the correction to exhaustion.  For any two primes
  there is **an auxiliary prime, outside any prescribed finite set, modulo which both are power
  non-residues of the prescribed odd prime exponent**; multiplying a class by the two correctors it
  supplies kills its invariants at those two primes at the cost of one at the auxiliary prime, so
  the number of bad primes drops by one and never rises.  Descending on that number to the case of
  a single bad prime, where the splitting field itself can be chosen to miss it, gives **the total
  invariant of every Brauer class of the rationals of odd prime order is trivial** — global
  reciprocity over the rationals in that degree.
* `InverseGalois.CFT.Brauer.RealCorrector` removes the last restriction.  The quaternion algebra
  attached to minus one and the field of cube roots of unity is ramified at three, where its
  invariant is the class of one half, and the correction procedure applies to it only if it is
  split by the reals, which would leave that invariant uncancelled; so it is **a class of order two
  which the reals do not split and whose total invariant is trivial**, its two halves at three and
  at infinity cancelling.  Multiplying by it moves any class of two-power order into the ones the
  reals split, and Bézout splits an arbitrary order into its two-part and its odd part, giving
  **the total invariant of every Brauer class of the rationals is trivial** — global reciprocity
  over the rationals, in every degree and with no hypothesis at all.
* `InverseGalois.CFT.Brauer.NormPlaceValue` measures a norm.  The multiplicity of a height one
  prime in an ideal is additive on nonzero ideals, is one exactly at the prime itself, and is read
  off from the adic valuation; the relative norm carries a prime of an extension to the prime below
  it raised to the residue degree, and the residue degree of a prime over one it does not lie over
  vanishes, so **the multiplicity of a prime of the base in the relative norm of an ideal is the
  sum over all the primes of the extension of the residue degree times the multiplicity there**.
  Factoring an ideal into primes and writing an element as a quotient of algebraic integers turns
  that into a statement about values at places: **the value at a place of the base field of the
  norm of a nonzero element is the sum over the places of the extension of the residue degree over
  that place times the value there**.
* `InverseGalois.CFT.Brauer.ResidueCardDegree` counts the residues of a completion of an arbitrary
  number field.  Reducing an integer of the field in the residue ring of the completion is a ring
  homomorphism whose kernel is the place, because the valuation of an integer in the completion is
  its valuation in the field; and it is surjective, because the field is dense in its completion, so
  every integer of the completion differs from an integer of the field by something of valuation
  less than one.  Hence **the residue ring of a completion has as many elements as the residue field
  of the place**, and since the absolute norm of a place is the residue characteristic raised to the
  residue degree, **the completion of a number field at a place over `p` has `p` raised to the
  residue degree many residues**.  Over the rationals the residue degree is one and this is the
  earlier count.
* `InverseGalois.CFT.Brauer.PlaceFrobeniusDegree` frees the cyclotomic description of the Frobenius
  from the rationals.  The Frobenius raises a root of unity to the power given by the number of
  residues of the base, and that number is now known for an arbitrary base: so **the Frobenius of an
  unramified place raises a root of unity to the power of the rational prime below the place raised
  to the residue degree of the place of the base**, and **when the extension is generated by that
  root of unity the description determines the Frobenius**.  Feeding that into the local computation
  gives **the invariant at an unramified place of a cyclic algebra whose splitting field is
  generated by a root of unity**, over an arbitrary number field: the exponent expressing the
  Frobenius as a power of the chosen generator, times the value of the coefficient, divided by the
  degree.
* `InverseGalois.CFT.Brauer.PlaceSubcyclotomicBase` passes that computation to a subfield, over an
  arbitrary base.  The cyclic algebra of a subfield for the restricted generator is the cyclic
  algebra of the larger field for the coefficient raised to the relative degree; raising the
  coefficient to that degree multiplies its value by the same factor, and the degree of the larger
  field is the degree of the subfield times the relative degree, so the factor cancels in the
  rationals modulo the integers.  Hence **the invariant at an unramified finite place of a cyclic
  algebra over an arbitrary number field, split by a subfield of an extension generated by a root of
  unity**, is the exponent expressing the Frobenius as a power of the chosen generator, times the
  value of the coefficient, divided by the degree of the subfield.
* `InverseGalois.CFT.Brauer.PlaceSubcyclotomicPower` splits that exponent into a part depending on
  the rational prime and a part depending on the place.  Iterating an automorphism raises a root of
  unity to the iterated power of the exponent, and two powers of a root of unity agree when the
  exponents are congruent modulo its order; so a power of the generator raising the root of unity
  to the rational prime below the place raises it, once iterated as many times as the residue
  degree, to the number of residues of the base.  Hence **the invariant at an unramified finite
  place, with the exponent split as a rational exponent times the residue degree of the place**,
  which confines the dependence on the place to a single natural number.
* `InverseGalois.CFT.Brauer.InertiaDegRat` compares the two ways of measuring that residue degree.
  The absolute norm of an ideal is the absolute norm of the ideal below it raised to the residue
  degree, and it is also the rational prime raised to the residue degree over the integers; every
  finite place of the rationals has residue degree one, so the absolute norm of the place of the
  rationals below is the prime itself, and **the residue degree of a place over the ideal generated
  by the rational prime below it is its residue degree over the place of the rationals below it**.
* `InverseGalois.CFT.Brauer.PlaceSubcyclotomicFibre` measures the exponent that way.  The local
  computation counts residues as powers of the rational prime, whereas adding up the invariants
  above one rational prime takes norms relative to the integers of the rationals; the two residue
  degrees agree, so **the invariant at an unramified finite place, with the residue degree measured
  against the place of the rationals below**, takes the shape in which a whole fibre can be summed.
* `InverseGalois.CFT.Brauer.ResidueGenerator` prepares the ramified place over an arbitrary base.
  The Teichmüller lift of a generator of the residues is a root of unity of order one less than the
  number of residues whose powers meet every element of absolute value one, so its power of
  complementary exponent has order the exponent, and a prescribed root of unity of that order is a
  power of it with exponent prime to the order.  Reduction of the units of one cyclic group of
  residues onto the units of a quotient is surjective, so that exponent lifts to one prime to the
  order of the Teichmüller lift, and the corresponding power of the lift is still a generator.
  Hence **a root of unity of order dividing one less than the number of residues is the power of
  complementary exponent of a generator of the residues**, for the absolute value of a complete
  field and for the valuation of a completion of a number field alike.
* `InverseGalois.CFT.Brauer.PlaceConductorBase` reads the ramified place over an arbitrary base.  A
  rational prime unramified at a place of a number field is a uniformiser of the completion there,
  because the valuation of a rational prime is the exponential of minus the ramification index; so
  the radical of the opposite of an odd prime, which presents the completion of a subfield of the
  field generated by the primitive roots of unity of that prime, has a uniformiser as its
  coefficient, exactly as it does over the rationals.  What changes is the residue field, which is
  now an extension of the field with as many elements as the prime, of degree the residue degree of
  the place; the generator of its residues whose complementary power is the root of unity
  multiplying the radical comes from the root of unity itself rather than from a rational primitive
  root.  Naming the exponent by that generator is not stable under a change of place, so it is
  recorded by the congruence it satisfies, and **the invariant, at a place above an odd prime
  unramified in the base, of a cyclic algebra split by a subfield of the field generated by the
  primitive roots of unity of that prime, with a coefficient that is a unit there**, is the class of
  the exponent naming the coefficient raised to the complementary power of the degree as a power of
  that root of unity.
* `InverseGalois.CFT.Brauer.TotallyRealInvariantBase` clears the archimedean places over an
  arbitrary base.  A complex place splits everything, and a real place splits whatever embeds into
  the reals over the associated embedding of the base; an extension generated by a totally real
  subfield does, because the composite of that embedding with the inclusion of the reals into the
  complex numbers extends to the extension, and the extension of it agrees with its conjugate on the
  generating subfield, hence everywhere, so it is fixed by conjugation and factors through the
  reals.  A generating subfield is what the general base calls for, since an extension of a base
  with a complex place is never itself totally real, while the splitting fields the reciprocity
  computation uses are compositums of the base with a totally real field of the rationals.  So
  **a Brauer class of a number field split by an extension generated by a totally real subfield has
  trivial invariant at every infinite place**, and **its total invariant is the product of its
  invariants at the finite places** — in particular for a cyclic algebra with such a splitting
  field, which is the shape the reciprocity computation over an arbitrary base takes.
* `InverseGalois.CFT.Brauer.SplitBase` decides, over an arbitrary base, when a cyclic extension
  splits a Brauer class.  At a finite place the order of the decomposition group is the local
  degree, so in an extension of prime-power degree **a power of the prime divides the local degree
  at a place whose decomposition group is not killed by the next smaller power**, and that kills an
  invariant of that order.  At an archimedean place the condition comes from the base: a real place
  of the extension restricts to a real place of the base, and the two completions are the reals
  along compatible embeddings, so **a class with trivial invariant at every infinite place of the
  base is split by the completion of the extension at a real place**.  Together, **a class killed
  by a prime power, trivial at the infinite places, is split by a cyclic extension of prime-power
  degree whose decomposition group at every place carrying a nontrivial invariant is large
  enough** — the criterion the reciprocity computation over an arbitrary base feeds its auxiliary
  field into.
* `InverseGalois.CFT.Brauer.NormReduction` computes a norm componentwise and modulo a maximal ideal.
  An element of a finite product of algebras is the product of the elements agreeing with it in a
  single coordinate and equal to one elsewhere, and multiplication by such an element is
  multiplication by its one coordinate on the corresponding factor and the identity on the
  complementary product, so **the norm of an element of a finite product of algebras is the product
  of the norms of its components**.  Separately, a basis of an algebra reduces modulo an ideal of
  the base to a spanning family of the reduction, hence to a basis as soon as the reduction has the
  dimension the rank predicts; the coefficients in it are the reductions of the coefficients, so the
  matrix of multiplication reduces to the matrix of multiplication, and **the norm of an element
  reduces modulo a maximal ideal of the base to the norm of its reduction**.  Together these express
  the norm of an algebraic integer modulo a rational prime through the residue fields of the places
  above it, which is what compares the invariants of a cyclic algebra at the places over a prime
  with the invariant of its trace down to the rationals.
* `InverseGalois.CFT.Brauer.NormFactors` carries that reduction through to the individual places.
  The Chinese remainder theorem splits the reduction of an extension of Dedekind domains modulo a
  maximal ideal of the base as the product of the reductions modulo the powers of the primes lying
  over it to which they ramify, and that splitting respects the residue field of the base, so
  **the norm of an element reduces modulo a maximal ideal of the base to the product, over the
  primes lying over it, of the norms of the reductions modulo the corresponding ramified powers**.
  A separate computation records the shape of a norm of finite fields: it is a power, by the
  quotient of the orders of the two multiplicative groups, so **raising an element of a finite field
  to the power the order of its multiplicative group divided by a divisor of the order of the
  multiplicative group of a subfield is the norm to that subfield raised to the complementary
  power**.  This is what turns a power residue symbol computed in the residue field of a place into
  one computed in the prime field below it.
* `InverseGalois.CFT.Brauer.PlaceOrders` realises prescribed orders at finitely many places.  A
  prime of a Dedekind domain is contained neither in its own square nor in any other prime, so
  prime avoidance produces an element of it lying outside the union of its square with finitely many
  other primes, and **that element has multiplicity one at the prime and multiplicity zero at each
  of the others**.  Multiplying powers of such elements realises any prescribed system of
  multiplicities, and a quotient of two of them realises any prescribed system of orders, so
  **prescribed orders at finitely many finite places of a number field are realised by a single
  element of the field** and **any element can be corrected to have order zero at each of finitely
  many finite places**.  Since the class of a cyclic algebra is unchanged when its coefficient is
  multiplied by a norm, and a correcting factor of prescribed orders can be produced as such a norm,
  nothing is lost by computing the invariant only for a coefficient which is a unit at the places
  under consideration.
* `InverseGalois.CFT.Brauer.FibreInvariant` groups the places of a number field by the rational
  prime below them.  A product of exponentials of an additively written family is the exponential
  of its sum, so a product of invariants is read as a sum of exponents; over a single fibre those
  exponents are the residue degree times the value of the coefficient, the terms outside the fibre
  vanishing because the residue degree of a prime relative to a rational prime other than the one
  below it is zero, and the norm formula for values at places sums them.  Hence **the product of
  the invariants over the places above a rational prime is the exponential of the value at that
  prime of the norm of the coefficient**, hence **is the invariant at that prime** as soon as the
  latter is the exponential of the same exponent times the value there of the norm.  Globally, the
  interchange of a doubly indexed product of finite support expresses a product over the places of
  the number field as the product over the
  rational primes of the products over the places above them, so **the product of the invariants
  over all finite places agrees with a product over the rational primes** as soon as it does so
  fibre by fibre.  When the invariants above a prime are instead read off from residues, each of
  them being the exponential of an exponent naming a power of a fixed generator, **the product over
  the fibre is the exponential of the sum of those exponents**, the sum being finite because only
  finitely many places lie above a rational prime.
* `InverseGalois.CFT.Brauer.NormPrimesOver` specialises the Chinese remainder splitting of a norm to
  a number field.  The ring of integers of a number field is a finitely generated torsion free
  module over the integers of the rationals, which is a principal ideal ring, so it is free of rank
  the degree of the field, and that rank is the dimension over the residue field of the reduction
  modulo a rational prime; hence **the norm of an algebraic integer reduces modulo a rational prime
  to the product, over the primes of the ring of integers over it, of the norms of the reductions
  modulo the corresponding ramified powers**.  A place of a number field lies over a rational prime
  exactly when that prime is the one below it, so **the places above a rational prime match the
  primes over it** — in particular **only finitely many of them do** — and the product can be read
  as one over the fibre of the map sending a place to the rational prime below it, the shape in
  which the invariants of a class in the Brauer group are grouped.
* `InverseGalois.CFT.Brauer.ResidueCongruence` reads a local statement as a congruence.  The
  valuation of an integer of a number field in the completion at a place is its valuation there, so
  **two integers agree modulo a place exactly when their difference is small in the completion**;
  and since a power of a difference of small valuation is again small, **a power of an integer that
  is close to a power of a root of unity reduces modulo the place to the same power of the natural
  number representing that root**.  The completion has as many residues as the place, so the same
  statement is available with the power written as the local computation of an invariant produces
  it, by the number of residues of the completion.
* `InverseGalois.CFT.Brauer.FibreExponent` adds up the exponents naming the invariants above one
  rational prime.  Raising an element of a residue field to the number of its elements less one
  over the degree is the norm to the residue field below followed by the corresponding power there,
  so **the norm of the reduction of an integer at a place, raised to that power, is the power by
  the exponent naming the place of the natural number representing the root of unity**.  At an
  unramified prime, reduction modulo a place is reduction modulo the ramified power to which the
  Chinese remainder theorem splits the norm, so **the reduction of the norm of the integer, raised
  to that power, is the power of the natural number by the sum of the exponents over the places
  above the prime**.  The natural number has order the degree there, so an equality of its powers
  is a congruence: **the exponents above a rational prime add up, modulo the degree, to the
  exponent of the prime**.
* `InverseGalois.CFT.Brauer.FibreConductor` compares the invariants at the prime whose roots of
  unity generate the splitting field.  Each invariant above that prime, and the invariant at the
  prime itself, is the exponential of an exponent read from a residue congruence against a fixed
  generator of order the degree; the exponents above the prime add up to the one below it, so
  **the product of the invariants over the places above the prime is the invariant at the prime**
  as soon as the prime is unramified in the number field.
* `InverseGalois.CFT.Brauer.FibreTotal` passes from the fibres to the whole.  The total invariant
  of a class is the product of the invariants at the finite places once those at the infinite
  places are trivial, so **a class of a number field whose invariants above each rational prime
  multiply to the invariant there of a class of the rationals has the same total invariant as that
  class**, and in particular **has vanishing total invariant** as soon as the rational one does.
  This is the shape in which reciprocity over the rationals carries reciprocity over an arbitrary
  number field.
* `InverseGalois.CFT.Brauer.PlaceUnitValue` records when a unit stays a unit.  The value of a unit
  at a finite place is the logarithm of the valuation of its image in the completion, so **the
  value vanishes exactly when that valuation is one**; and the value of a norm at a place of the
  rationals is the sum over the places above it of the residue degree times the value there, so
  **the norm of a unit invertible at every place above a rational prime is invertible at that
  prime**.  This is what lets the same coefficient be fed to the local computation at the conductor
  simultaneously over a number field and over the rationals.
* `InverseGalois.CFT.Brauer.RatResidueOrder` names the residues of the rationals.  The residue ring
  at a place containing a prime has that prime as its number of elements and as its characteristic,
  so **two natural numbers have the same residue there exactly when they are congruent modulo the
  prime**; consequently **a power of a primitive root has as multiplicative order the complementary
  factor of its exponent in one less than the prime**.  This is the input that lets the exponents
  naming the invariants above a prime be compared with the exponent naming the invariant below.
* `InverseGalois.CFT.Brauer.RatBase` identifies the two ways of taking the rationals as a base.
  The rational integers extend to the integers of the rationals by an isomorphism, so **a place of
  the rationals is unramified over the rational integers**, and **the norm of an algebraic integer
  relative to the integers of the rationals is the norm of its image relative to the rationals**.
  The first lets the computation at the conductor over an arbitrary base be applied over the
  rationals themselves, the second lets the coefficient below be the norm of the coefficient above.
* `InverseGalois.CFT.Brauer.BaseSubcyclotomic` carries reciprocity from the rationals to an
  arbitrary number field for the cyclic algebras built from the roots of unity of an odd prime.
  The invariant at the place of the conductor of such an algebra is packaged over an arbitrary base
  as **the class of the exponent that expresses the coefficient as a power residue there**, so that
  the two sides of the comparison are two instances of one statement.  Both splitting fields are
  generated by a totally real field, so the infinite places contribute nothing; away from the
  conductor the invariants above a rational prime are read from one exponent weighted by the
  residue degrees, which add up with the values to the value of the norm; and at the conductor the
  exponents naming the power residues above the prime add up to the exponent naming the power
  residue of the norm.  Hence **the total invariant of a cyclic algebra over a number field split
  by a subfield of the field of the primitive roots of unity of an odd prime, with an integral
  coefficient that is a unit above that prime, vanishes**.
* `InverseGalois.CFT.BaseTotallyRamified` transfers total ramification into a compositum, the
  direction opposite to the transfer of unramifiedness.  **The ramification index is multiplicative
  in a tower of number fields**, so it can be computed along either side of the compositum square:
  up through the Galois extension of the rationals it is divisible by the degree of that extension
  when that extension is totally ramified, and up through the new base field it is unchanged when
  the place is unramified there.  That degree therefore divides the ramification index of the
  compositum over the new base, which is the order of an inertia subgroup and so at most the degree
  of the compositum over the new base, itself at most the degree of the original extension because
  restriction of automorphisms is injective.  The inequalities close up, and **total ramification in
  a Galois extension of the rationals passes to a compositum with a number field in which the place
  is unramified**.
* `InverseGalois.CFT.Brauer.BaseCyclotomic` discharges the arithmetic hypotheses of the comparison
  theorem in the case that matters, where the top field is the compositum of the base with the
  field of the primitive roots of unity of a prime that is unramified in the base.  A cyclotomic
  field of prime conductor is ramified only at that conductor, so its ramified set is disjoint from
  that of the base; the degrees of the two sides of the compositum square therefore agree, total
  ramification at the conductor is inherited by the compositum and unramifiedness away from the
  conductor is inherited too, and a place above the conductor, being totally ramified, is fixed by
  every automorphism.  Hence **the total invariant of a cyclic algebra over a number field split by
  the compositum of the base with a cyclotomic field of prime conductor unramified in the base is
  trivial**, on the sole arithmetic hypothesis that **a rational prime outside the ramified set of
  a number field is unramified at every place above it**.
* `InverseGalois.CFT.Brauer.PrescribedValue` gives the places of a number field whatever values one
  likes.  The Chinese remainder theorem supplies an algebraic integer congruent, modulo one more
  than the prescribed power of each of finitely many chosen primes, to that power of a uniformiser
  there, and the correction has too small a valuation to disturb the leading term, so **an element
  of a Dedekind domain may be given prescribed valuations at finitely many places**; a quotient of
  two such integers then gives **a unit of a number field with prescribed values at finitely many
  places**.  The construction also clears denominators without disturbing a finite set of places,
  so **a unit trivial at finitely many places is a quotient of two algebraic integers trivial
  there**.
* `InverseGalois.CFT.Brauer.NormAdjust` exploits total ramification to compute norms.  If the
  inertia group at a place of a Galois extension is the whole Galois group then the number of
  places above the place beneath it and the residue degree there are both one, since those two
  numbers and the order of the inertia group multiply to the order of the Galois group; so **a
  place whose inertia group is the whole Galois group is the only place above the place beneath it,
  and has residue degree one**, and the value of a norm at the place below is exactly the value of
  the element at the place above.  Since values at finitely many places may be prescribed at will,
  **the norms realise every family of values at the places above a totally ramified prime**.  A
  rational prime unramified in the base and totally ramified in a Galois extension of the rationals
  is totally ramified in the compositum, so for a homomorphism to the Brauer group that kills the
  norms an arbitrary unit may be adjusted to be a unit at that prime and then written as a quotient
  of algebraic integers which are units there: **trivial total invariant on those algebraic
  integers forces trivial total invariant on every unit**.
* `InverseGalois.CFT.Brauer.BaseCyclicClass` assembles the correcting classes themselves over an
  arbitrary number field.  The group of residues prime to a prime conductor is the Galois group of
  the cyclotomic field of that conductor, so **every residue prime to the conductor is a power of a
  fixed generating residue**; the residue cardinality of a place away from the conductor is such a
  residue, and the exponent expressing it scales the valuation, so **the invariant of a cyclic
  class at a finite place of the base lying over a rational prime other than the conductor is the
  valuation of the coefficient times that exponent**.  Composing the base with a totally real
  subfield of prescribed degree of the cyclotomic field then produces **the correcting Brauer
  classes of a number field**: a homomorphism from the units of the base to its Brauer group whose
  classes are killed by the prescribed degree, are trivial at every archimedean place, have trivial
  total invariant, and have those prescribed invariants at the finite places away from the
  conductor.
* `InverseGalois.CFT.Brauer.DecompositionTransfer` compares a decomposition group of a compositum
  with the decomposition group of the factor that is an extension of the rationals.  The stabiliser
  of a place in the Galois group of an extension of the rationals is the decomposition group there,
  and its order is the residue degree once the prime is unramified, so **the residue degree of a
  place of a subfield of a cyclotomic field divides the order of the stabiliser of a place of the
  compositum**.  Multiplicativity of the residue degree in a tower bounds the residue degree of the
  compositum by the residue degree of the base times that stabiliser order, and the degree of the
  base bounds its own residue degree; so **a power of a prime dividing a product of a bounded
  number and a prime power is bounded by the multiplicity of the prime in the bound plus the
  exponent**, which is the arithmetic that converts a decomposition condition over the rationals
  into one over an arbitrary base.
* `InverseGalois.CFT.Brauer.BaseSubcyclotomicSplit` turns those comparisons into reciprocity over an
  arbitrary number field for a class of prime-power order.  Composing the base with the subfield of
  prescribed prime-power degree of the cyclotomic field of an auxiliary prime gives a cyclic
  extension satisfying reciprocity, and the order of its decomposition group at a place is, up to
  the residue degree contributed by the base, the order named by a power residue symbol.  Enlarging
  the exponent of the auxiliary congruence by the multiplicity of the prime in the degree of the
  base therefore absorbs that contribution, and **the invariants of a Brauer class of a number
  field, of prime-power order and trivial at the infinite places, add up to zero as soon as every
  rational prime below a place carrying a nontrivial invariant fails a power residue condition
  modulo an auxiliary prime**.
* `InverseGalois.NumberTheory.SplitDensityFamily` widens the density bound behind the choice of an
  auxiliary prime from one exceptional field to a whole family of them.  Iterating the subadditivity
  of a Dirichlet series along a finite index set bounds **the density of a set of primes covered by
  a finite set together with a finite family of others by the sum of the densities of the family**,
  so **infinitely many primes split completely in a Galois number field and in none of a finite
  family of larger ones** as soon as the reciprocals of the larger degrees do not add up to the
  reciprocal of the smaller one.  The enlargement factor of each larger field only has to exceed the
  number of conditions imposed, which is what lets a single prime carry arbitrarily many
  simultaneous non-residue conditions.
* `InverseGalois.CFT.Scholz.AuxPrimeFamily` produces that prime.  Over the cyclotomic field of a
  power of an odd prime a rational prime that is not an `ℓ`-th power there stays one after adjoining
  a root of unity of the wanted order, so **the radical field of the corresponding prime power has
  the full degree above the cyclotomic field**, and the family density bound applies to the whole
  list at once.  Hence, for a list of primes shorter than a power of `ℓ`, **there is a prime
  congruent to one modulo twice an arbitrarily large power of `ℓ`, avoiding any prescribed finite
  set, modulo which every prime on the list fails to be a power residue at that exponent**.
* `InverseGalois.CFT.Scholz.TwoPowerRadical` supplies the missing irreducibility at the prime two.
  For an odd prime the polynomial `X` raised to a prime power, minus a constant without a root of
  prime exponent, is irreducible; at two the honest criterion also involves the constant modulo
  fourth powers of minus four, and that correction disappears over a field already containing a
  square root of minus one, since minus four is then a fourth power there.  Adjoining one square
  root of the constant, a square root of it would have a norm whose square is minus the constant,
  and the square root of minus one turns that norm into a square root of the constant; so the
  induction on the exponent, run over all fields at once, gives **`X` raised to a power of two,
  minus a non-square, is irreducible over a field containing a square root of minus one**.  Hence
  **a rational number without a square root in a field of matching roots of unity is enlarged by
  the full two-power factor**, and **a rational number with a square root but no fourth root there
  is still enlarged by half of it**, its two-power root being a root of half the order of an
  element already present.
* `InverseGalois.CFT.Scholz.DyadicAuxPrimeFamily` runs the family density argument at the prime
  two.  Over the cyclotomic field of a two-power conductor only two ramifies, so an odd prime has
  no square root there and its radical of two-power exponent multiplies the degree by that whole
  exponent; two itself does have a square root there once the conductor is at least eight, an
  explicit one being a primitive eighth root of unity plus its inverse, but no fourth root, so its
  radical still multiplies the degree by half the exponent.  The uniform factor of half the
  exponent grows without bound while the number of prescribed primes does not, so the union bound
  succeeds for all of them at once and yields **a prime congruent to one modulo a prescribed power
  of two, avoiding any prescribed finite set, modulo which every prime on a list shorter than half
  the exponent fails to be a power residue at that exponent**.
* `InverseGalois.CFT.Brauer.BaseOddReciprocity` closes global reciprocity over an arbitrary number
  field in odd order.  A class has nontrivial invariants at only finitely many places, hence above
  only finitely many rational primes, and the exponent at which those primes are asked to be
  non-residues may be raised at will by raising the degree of the auxiliary cyclotomic subfield; so
  a single auxiliary prime discharges the hypothesis of the splitting criterion for all of them
  simultaneously, and the archimedean invariants of a class of odd order are trivial because the
  Brauer group of the reals is killed by two.  Hence **the invariants of a Brauer class of a number
  field of odd prime-power order add up to zero**, and, splitting an arbitrary odd order at its
  least prime factor and recombining by a Bézout relation, **the invariants of a Brauer class of a
  number field of odd order add up to zero**.
* `InverseGalois.CFT.Brauer.RealCyclicSign` reads the archimedean invariants of a quadratic cyclic
  algebra as signs.  The complex numbers are a quadratic extension of the reals generated by
  conjugation, so a real unit produces a cyclic algebra whose class is trivial exactly when the unit
  is a norm, that is exactly when it is positive: the resulting invariant is **the sign of the
  unit**, and two units of the same sign share it.  Over an arbitrary number field whose splitting
  field is a quadratic extension with no real place, the splitting field embeds into the complex
  numbers over the completion at a real place and the embedding is not real, so restriction is an
  injection between two groups of order two, hence an isomorphism carrying conjugation to the chosen
  generator; base change along it therefore keeps the coefficient, and **the invariant at a real
  place of such an algebra is the sign of the coefficient there**.  Multiplying over all the
  infinite places and comparing with the archimedean half of the product formula, where the complex
  places contribute a positive factor to the norm, gives **the archimedean invariants of such an
  algebra multiply out to the archimedean invariant over the rationals of the algebra attached to
  the norm of the coefficient** — the archimedean comparison that reciprocity over an arbitrary base
  needs in degree two, where no totally real splitting field is available.
* `InverseGalois.CFT.Cyclotomic.ImaginarySubfield` supplies the splitting field that comparison
  wants.  Complex conjugation of a CM field is an automorphism of order two, and an embedding of an
  intermediate field into the complex numbers extends to the whole field, where it carries that
  conjugation to conjugation of the complex numbers; so **an intermediate field that complex
  conjugation moves is totally complex**, and complex conjugation moves every intermediate field
  over which the ambient field has odd degree, its fixing group then having odd order.  Inside the
  cyclotomic field of prime conductor this is an arithmetic condition on the degree, and it produces
  **a totally complex subfield of prescribed degree of the cyclotomic field of a prime conductor**,
  totally ramified there and with the same power residue splitting law as its totally real
  counterpart, whenever the complementary degree is odd.
* `InverseGalois.CFT.Brauer.BaseSignCorrector` assembles the two into the corrections that
  reciprocity in the two-primary case consumes.  The comparison of a cyclic algebra over a number
  field with its counterpart over the rationals is first freed of the assumption that both splitting
  fields are totally real, the archimedean comparison becoming a hypothesis; then it is discharged
  in the totally complex quadratic case by the sign computation.  Composing the base with the
  imaginary quadratic subfield of the cyclotomic field of a prime conductor congruent to three
  modulo four and unramified in the base gives a totally complex quadratic extension, and its cyclic
  algebras are **classes killed by two, of trivial total invariant, whose invariant at a real place
  is the sign of the coefficient there** — corrections able to realise any prescribed pattern of
  archimedean invariants, as no class pulled back from the rationals could.
* `InverseGalois.CFT.Brauer.BaseReciprocity` completes global reciprocity over an arbitrary number
  field.  The odd part of the order is already settled, and what the two-primary part needs is a way
  to clear the archimedean invariants before the auxiliary prime argument applies.  The real places
  of a number field are independent as far as signs are concerned: a generator of the field takes
  distinct real values at them, and cutting out a short interval around one of those values with a
  pair of rationals produces an element negative at that place alone, so every pattern of signs is
  realised by a unit.  Feeding such a unit to a sign corrector, whose conductor is one of the
  infinitely many primes congruent to three modulo four, yields a class matching the archimedean
  behaviour of the given one; their product is of two-power order, split by every completion at an
  infinite place, and has the same total invariant.  Splitting an arbitrary finite order into its
  two-part and its odd part then gives **global reciprocity over a number field: the invariants of a
  Brauer class add up to zero**.
* `InverseGalois.CFT.Brauer.CyclicProduct` reads reciprocity on the classes that carry the
  arithmetic.  A cyclic algebra and the power residue symbol of two units both have a Brauer class
  over the base, so the invariants of either multiply to one over all places; only finitely many of
  the finite places contribute, and the statement can be read over any finite set carrying them
  together with the finitely many archimedean terms.  That is **the product formula for the norm
  residue symbol**.  The same base change identifies what a single factor measures: over a
  completion the cyclic algebra becomes the cyclic algebra of the decomposition group with the same
  coefficient, and a cyclic algebra is split exactly when its coefficient is a norm, so **the
  invariant at a finite place vanishes precisely when the coefficient is a norm from the completion
  of the splitting field there**.  The product formula is then the statement that the failures to
  be a local norm cancel.
* `InverseGalois.CFT.Brauer.InfiniteCyclic` supplies the archimedean half of that local reading.
  The two-step base change through the decomposition field works verbatim at an infinite place: the
  decomposition group is a subgroup of a finite cyclic group, hence generated by the power of the
  global generator by its index, and the automorphism group of the completions is that
  decomposition group, so **extending scalars to the completion at an infinite place sends a cyclic
  algebra to the cyclic algebra of the decomposition group with the same coefficient**.  Read
  through the invariant, **the invariant at an infinite place vanishes exactly when the coefficient
  is a norm from the completion of the splitting field there**.
* `InverseGalois.CFT.Brauer.HasseNorm` puts the two local readings together with the theorem of
  Albert, Brauer, Hasse and Noether.  For a cyclic extension of number fields the coefficient of a
  cyclic algebra is a norm exactly when the algebra is split, so being a norm globally forces every
  local invariant to vanish, and conversely a class all of whose local invariants vanish is trivial.
  Since every place of the base carries a place of the extension above it, the local conditions can
  be quantified over the primes and infinite places of the extension.  The result is **the Hasse
  norm theorem: an element of the base field of a cyclic extension of number fields is a norm
  exactly when it is a norm from the completion of the extension at every place**.
-/
