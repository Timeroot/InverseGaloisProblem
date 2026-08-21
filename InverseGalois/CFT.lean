import InverseGalois.CFT.Brauer.Group
import InverseGalois.CFT.Brauer.Opposite
import InverseGalois.CFT.Brauer.TensorSimple
import InverseGalois.CFT.Cyclotomic.BuildingBlock
import InverseGalois.CFT.Cyclotomic.Chebotarev
import InverseGalois.CFT.Cyclotomic.CyclicSubfield
import InverseGalois.CFT.Cyclotomic.Frobenius
import InverseGalois.CFT.Cyclotomic.OnePrimeRamified
import InverseGalois.CFT.Cyclotomic.PrimeSelection
import InverseGalois.CFT.Cyclotomic.Ramified
import InverseGalois.CFT.Cyclotomic.Splitting
import InverseGalois.CFT.GroupCohomology.OfCocycle
import InverseGalois.CFT.GroupCohomology.ToCocycle
import InverseGalois.CFT.Level
import InverseGalois.CFT.Unramified

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

## Reciprocity for the rational field

* `InverseGalois.CFT.Cyclotomic.Frobenius` identifies the Frobenius at a prime `p ∤ n` of `ℚ(ζₙ)`
  with the class of `p` in `(ℤ/nℤ)ˣ`: the reciprocity law for the rational field.
* `InverseGalois.CFT.Cyclotomic.Splitting` reads off from it that `p` splits completely in `ℚ(ζₙ)`
  exactly when `p ≡ 1 mod n`.
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

## Group extensions and the Brauer group

* `InverseGalois.CFT.GroupCohomology.OfCocycle` turns a multiplicative `2`-cocycle into a group
  extension, and `InverseGalois.CFT.GroupCohomology.ToCocycle` turns a group extension into its
  cohomology class, splitting exactly when the class vanishes.
* `InverseGalois.CFT.Brauer.TensorSimple` proves that the tensor product of two central simple
  algebras is central simple, the multiplication of the Brauer group.
* `InverseGalois.CFT.Brauer.Opposite` proves that a central simple algebra tensored with its
  opposite is a matrix algebra, the inversion of the Brauer group.
* `InverseGalois.CFT.Brauer.Group` assembles the two into the abelian group structure on
  `BrauerGroup K`.
-/
