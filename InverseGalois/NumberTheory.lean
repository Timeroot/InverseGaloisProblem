import InverseGalois.NumberTheory.IdealEulerProduct
import InverseGalois.NumberTheory.IdealNormCount
import InverseGalois.NumberTheory.IntegerPointsSublinear
import InverseGalois.NumberTheory.PrimeLowerBound
import InverseGalois.NumberTheory.SplitCompletely
import InverseGalois.NumberTheory.SplitDensity

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
-/
