import Mathlib
import InverseGalois.CFT.Global.HilbertPlaces
import InverseGalois.CFT.Local.PadicHilbertMul

/-!
# Multiplicativity of the Hilbert symbol of a rational pair at an odd place

The local symbol of two `p`-adic numbers is multiplicative in each argument as soon as the residue
characteristic is odd.  Transporting that statement along the embedding of the rationals into the
field of `p`-adic numbers gives multiplicativity of the symbol of a rational pair at every odd
finite place.

## Main results

* `InverseGalois.CFT.hilbertSymbolAt_mul_left`: at an odd place the symbol is multiplicative in
  its first argument.
* `InverseGalois.CFT.hilbertSymbolAt_mul_right`: at an odd place the symbol is multiplicative in
  its second argument.
-/

namespace InverseGalois.CFT

open Local

/-- **At an odd finite place the symbol of a rational pair is multiplicative in its first
argument.** -/
theorem hilbertSymbolAt_mul_left {p : Nat.Primes} (hp : (p : ℕ) ≠ 2) {a a' b : ℚ}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertSymbolAt p (a * a') b = hilbertSymbolAt p a b * hilbertSymbolAt p a' b := by
  have hA : ((a : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using ha
  have hA' : ((a' : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using ha'
  have hB : ((b : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hb
  unfold hilbertSymbolAt
  push_cast
  exact hilbertSymbol_padic_mul_left hp hA hA' hB

/-- **At an odd finite place the symbol of a rational pair is multiplicative in its second
argument.** -/
theorem hilbertSymbolAt_mul_right {p : Nat.Primes} (hp : (p : ℕ) ≠ 2) {a b b' : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSymbolAt p a (b * b') = hilbertSymbolAt p a b * hilbertSymbolAt p a b' := by
  rw [hilbertSymbolAt_comm p a (b * b'), hilbertSymbolAt_comm p a b, hilbertSymbolAt_comm p a b',
    hilbertSymbolAt_mul_left hp hb hb' ha]

end InverseGalois.CFT
