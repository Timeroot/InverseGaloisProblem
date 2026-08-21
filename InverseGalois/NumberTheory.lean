import InverseGalois.NumberTheory.IdealNormCount
import InverseGalois.NumberTheory.IntegerPointsSublinear
import InverseGalois.NumberTheory.PrimeLowerBound
import InverseGalois.NumberTheory.SplitCompletely

/-!
# Number-theoretic estimates

* `InverseGalois.NumberTheory.IdealNormCount` counts the ideals of a ring of integers of a given
  absolute norm, shows the count is multiplicative, and derives the Euler product for the Dedekind
  zeta function.
* `InverseGalois.NumberTheory.IntegerPointsSublinear` and
  `InverseGalois.NumberTheory.PrimeLowerBound` are elementary estimates used by the specialization
  arguments.
* `InverseGalois.NumberTheory.SplitCompletely` proves Schur's theorem on prime divisors of
  polynomial values and deduces that infinitely many rational primes split completely in a number
  field that is Galois over `ℚ`.
-/
