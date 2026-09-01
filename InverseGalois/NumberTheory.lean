import InverseGalois.NumberTheory.IdealEulerProduct
import InverseGalois.NumberTheory.IdealNormCount
import InverseGalois.NumberTheory.IntegerPointsSublinear
import InverseGalois.NumberTheory.PrimeLowerBound
import InverseGalois.NumberTheory.RelativeSplitDensity
import InverseGalois.NumberTheory.SplitCompletely
import InverseGalois.NumberTheory.SplitDensity
import InverseGalois.NumberTheory.SplitDensityPair
import InverseGalois.NumberTheory.SplitReduction
import InverseGalois.NumberTheory.SplitSubfield

/-!
# Number-theoretic estimates

* `InverseGalois.NumberTheory.IdealNormCount` counts the ideals of a ring of integers of a given
  absolute norm, shows the count is multiplicative, and derives the Euler product for the Dedekind
  zeta function indexed by the rational primes.
* `InverseGalois.NumberTheory.IdealEulerProduct` proves the Euler product in its intrinsic form,
  indexed by the prime ideals of the ring of integers.
* `InverseGalois.NumberTheory.IntegerPointsSublinear` and
  `InverseGalois.NumberTheory.PrimeLowerBound` are elementary estimates used by the specialization
  arguments.
* `InverseGalois.NumberTheory.SplitCompletely` proves Schur's theorem on prime divisors of
  polynomial values and deduces that infinitely many rational primes split completely in a number
  field that is Galois over `ℚ`.
* `InverseGalois.NumberTheory.SplitDensity` sharpens that to a density statement: the primes that
  split completely in a Galois number field of degree `n` have Dirichlet density `1/n`, so that of
  two Galois number fields of different degrees, infinitely many primes split completely in the
  smaller but not in the larger.
* `InverseGalois.NumberTheory.SplitDensityPair` iterates the union bound behind that comparison:
  the density of a set of primes covered by a finite set together with two others is at most the
  sum of their two densities, so infinitely many primes split completely in a Galois number field
  and in neither of two larger ones as soon as the reciprocals of the two larger degrees do not
  add up to the reciprocal of the smaller.
* `InverseGalois.NumberTheory.RelativeSplitDensity` carries that density statement over an
  arbitrary number field: the primes of the base that split completely in a Galois extension of
  degree `n` have Dirichlet density `1/n` among the primes of the base, so that of two Galois
  extensions of different degrees, infinitely many primes of the base split completely in the
  smaller but not in the larger.
* `InverseGalois.NumberTheory.SplitReduction` turns a completely split prime `q` into a ring
  homomorphism from the ring of integers onto `ZMod q` fixing the rational integers, so that
  radicals and roots of unity in the field descend to `ZMod q`.
* `InverseGalois.NumberTheory.SplitSubfield` transports complete splitting along an embedding of
  number fields: a prime that splits completely in the larger field splits completely in the
  smaller one, in particular in any intermediate field.
-/
