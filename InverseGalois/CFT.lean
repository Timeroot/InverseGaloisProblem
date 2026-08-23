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
import InverseGalois.CFT.GroupCohomology.Cohomologous
import InverseGalois.CFT.GroupCohomology.Corestriction
import InverseGalois.CFT.GroupCohomology.Cyclic
import InverseGalois.CFT.GroupCohomology.CyclicH2
import InverseGalois.CFT.GroupCohomology.CyclicSurjective
import InverseGalois.CFT.GroupCohomology.OfCocycle
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
import InverseGalois.CFT.Level
import InverseGalois.CFT.Local.DyadicAnisotropic
import InverseGalois.CFT.Local.DyadicHilbert
import InverseGalois.CFT.Local.DyadicHilbertMul
import InverseGalois.CFT.Local.DyadicNondegenerate
import InverseGalois.CFT.Local.DyadicQuaternary
import InverseGalois.CFT.Local.DyadicNormFive
import InverseGalois.CFT.Local.DyadicQuinary
import InverseGalois.CFT.Local.HilbertIdentities
import InverseGalois.CFT.Local.HilbertMap
import InverseGalois.CFT.Local.HilbertMul
import InverseGalois.CFT.Local.HilbertSymbol
import InverseGalois.CFT.Local.LegendreHilbert
import InverseGalois.CFT.Local.OddAnisotropic
import InverseGalois.CFT.Local.PadicHilbert
import InverseGalois.CFT.Local.PadicHilbertMul
import InverseGalois.CFT.Local.PadicLocalField
import InverseGalois.CFT.Local.PadicSquares
import InverseGalois.CFT.Local.PadicSquaresTwo
import InverseGalois.CFT.Local.RamifiedNormForm
import InverseGalois.CFT.Local.UnramifiedNormForm
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
import InverseGalois.CFT.TameCharacter
import InverseGalois.CFT.TameRamification
import InverseGalois.CFT.Tate.Basic
import InverseGalois.CFT.Tate.Exact
import InverseGalois.CFT.Tate.Herbrand
import InverseGalois.CFT.Tate.Hexagon
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
* `InverseGalois.CFT.Tate.Exact` records the counting principle behind the hexagon: in a cyclic
  exact sequence of six finite commutative groups the orders in odd and in even position have the
  same product.
* `InverseGalois.CFT.Tate.Hexagon` builds the two connecting maps of a short exact sequence of
  modules over a cyclic group and proves the resulting six-term sequence exact at each corner.
* `InverseGalois.CFT.Tate.Herbrand` defines the Herbrand quotient as the ratio of the orders of the
  two Tate groups, and shows it multiplicative in short exact sequences and trivial on finite
  modules, so that finite submodules and finite quotients may be discarded when computing it.
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
-/
