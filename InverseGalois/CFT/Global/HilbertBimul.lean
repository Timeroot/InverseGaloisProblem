import Mathlib
import InverseGalois.CFT.Global.HilbertMulPlaces
import InverseGalois.CFT.Global.HilbertProduct
import InverseGalois.CFT.Local.DyadicHilbertMul

/-!
# The product of the local Hilbert symbols is bimultiplicative

At every place of the rational field the Hilbert symbol is multiplicative in each argument: at the
real place because a product of reals is negative exactly when one factor is, at an odd finite
place because the norm form of an unramified or ramified quadratic extension is detected by the
valuation and a quadratic character, and at the dyadic place because the symbol is read off from
the residues modulo eight of the unit parts.  Multiplying these statements together over all
places — legitimate because only finitely many factors differ from one — makes the product over
all places bimultiplicative.

## Main results

* `InverseGalois.CFT.hilbertSymbolAt_mul_left'`: multiplicativity at an arbitrary finite place.
* `InverseGalois.CFT.hilbertProduct_mul_left`, `InverseGalois.CFT.hilbertProduct_mul_right`: the
  product over all places is multiplicative in each argument.
-/

namespace InverseGalois.CFT

open Local

/-- **At every finite place the symbol of a rational pair is multiplicative in its first
argument.** -/
theorem hilbertSymbolAt_mul_left' {p : Nat.Primes} {a a' b : ℚ}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertSymbolAt p (a * a') b = hilbertSymbolAt p a b * hilbertSymbolAt p a' b := by
  rcases eq_or_ne (p : ℕ) 2 with hp | hp
  · have hpe : p = (⟨2, Nat.prime_two⟩ : Nat.Primes) := Subtype.ext hp
    subst hpe
    have hA : ((a : ℚ_[2])) ≠ 0 := by simpa using ha
    have hA' : ((a' : ℚ_[2])) ≠ 0 := by simpa using ha'
    have hB : ((b : ℚ_[2])) ≠ 0 := by simpa using hb
    unfold hilbertSymbolAt
    push_cast
    exact hilbertSymbol_dyadic_mul_left hA hA' hB
  · exact hilbertSymbolAt_mul_left hp ha ha' hb

/-- **At every finite place the symbol of a rational pair is multiplicative in its second
argument.** -/
theorem hilbertSymbolAt_mul_right' {p : Nat.Primes} {a b b' : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSymbolAt p a (b * b') = hilbertSymbolAt p a b * hilbertSymbolAt p a b' := by
  rw [hilbertSymbolAt_comm p a (b * b'), hilbertSymbolAt_comm p a b, hilbertSymbolAt_comm p a b',
    hilbertSymbolAt_mul_left' hb hb' ha]

/-- **The product over all places is multiplicative in its first argument.** -/
theorem hilbertProduct_mul_left {a a' b : ℚ} (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertProduct (a * a') b = hilbertProduct a b * hilbertProduct a' b := by
  have hR : ((a : ℝ)) ≠ 0 := by simpa using ha
  have hR' : ((a' : ℝ)) ≠ 0 := by simpa using ha'
  have hRb : ((b : ℝ)) ≠ 0 := by simpa using hb
  have hcongr : ∀ p : Nat.Primes,
      hilbertSymbolAt p (a * a') b = hilbertSymbolAt p a b * hilbertSymbolAt p a' b :=
    fun p => hilbertSymbolAt_mul_left' ha ha' hb
  unfold hilbertProduct
  rw [show (((a * a' : ℚ)) : ℝ) = (a : ℝ) * (a' : ℝ) by push_cast; ring,
    hilbertSymbol_real_mul_left _ _ _ hR hR' hRb, finprod_congr hcongr,
    finprod_mul_distrib (finite_mulSupport_hilbertSymbolAt ha hb)
      (finite_mulSupport_hilbertSymbolAt ha' hb)]
  ring

/-- **The product over all places is multiplicative in its second argument.** -/
theorem hilbertProduct_mul_right {a b b' : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertProduct a (b * b') = hilbertProduct a b * hilbertProduct a b' := by
  rw [hilbertProduct_comm a (b * b'), hilbertProduct_comm a b, hilbertProduct_comm a b',
    hilbertProduct_mul_left hb hb' ha]

end InverseGalois.CFT
