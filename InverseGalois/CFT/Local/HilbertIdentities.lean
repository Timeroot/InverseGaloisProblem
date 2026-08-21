import Mathlib
import InverseGalois.CFT.Local.HilbertMul

/-!
# Elementary identities for the Hilbert symbol

The conic `⟨a, -a⟩` always has a rational point, so `-a` is a norm from `K(√a)` whenever the
question makes sense.  Because the norms form a group — this is the composition law of the binary
norm form — one may multiply the second argument of the Hilbert symbol by `-a` without changing
it.  Three consequences are recorded here: the symbol of `a` against `-a b` agrees with the symbol
of `a` against `b`, the symbol of `a` against itself is the symbol of `a` against `-1`, and the
symbol of `a` against `-1` measures whether `-1` is a norm.

These identities let one replace a pair of arguments both of positive valuation by a pair with
one unit argument, which is how the computation of a local symbol is reduced to the case of a
uniformiser against a unit.

## Main results

* `InverseGalois.CFT.Local.hilbertSymbol_neg_mul_right`: the second argument may be multiplied by
  the negative of the first.
* `InverseGalois.CFT.Local.hilbertSymbol_neg_mul_left`: the mirror statement.
* `InverseGalois.CFT.Local.hilbertSymbol_self`: the symbol of an element against itself is its
  symbol against `-1`.
-/

namespace InverseGalois.CFT.Local

variable {K : Type*} [Field K]

/-- **The second argument of the Hilbert symbol may be multiplied by the negative of the first.**
The element `-a` is a norm from `K(√a)`, and the norms form a group. -/
theorem hilbertSymbol_neg_mul_right (a b : K) (ha : a ≠ 0) :
    hilbertSymbol a (-a * b) = hilbertSymbol a b :=
  hilbertSymbol_mul_right_of_eq_one (neg_ne_zero.2 ha) (hilbertSymbol_neg_self a) b

/-- The same identity, with the sign written outside the product. -/
theorem hilbertSymbol_neg_mul_right' (a b : K) (ha : a ≠ 0) :
    hilbertSymbol a (-(a * b)) = hilbertSymbol a b := by
  rw [show -(a * b) = -a * b by ring, hilbertSymbol_neg_mul_right a b ha]

/-- **The first argument of the Hilbert symbol may be multiplied by the negative of the second.** -/
theorem hilbertSymbol_neg_mul_left (a b : K) (hb : b ≠ 0) :
    hilbertSymbol (-b * a) b = hilbertSymbol a b := by
  rw [hilbertSymbol_comm (-b * a) b, hilbertSymbol_neg_mul_right b a hb, hilbertSymbol_comm]

/-- **The Hilbert symbol of an element against itself is its symbol against `-1`.** -/
theorem hilbertSymbol_self (a : K) (ha : a ≠ 0) :
    hilbertSymbol a a = hilbertSymbol a (-1) := by
  have h := hilbertSymbol_neg_mul_right a (-1) ha
  rw [show -a * -1 = a by ring] at h
  exact h

/-- The symbol of `a` against `-a b` and against `b` agree, in the form in which the first
argument is recovered from a product of two elements of positive valuation. -/
theorem hilbertSymbol_neg_mul_mul (a b : K) (ha : a ≠ 0) :
    hilbertSymbol a (a * b) = hilbertSymbol a (-b) := by
  have h := hilbertSymbol_neg_mul_right a (-b) ha
  rw [show -a * -b = a * b by ring] at h
  exact h

end InverseGalois.CFT.Local
