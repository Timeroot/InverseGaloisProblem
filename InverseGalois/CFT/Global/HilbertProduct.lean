import Mathlib
import InverseGalois.CFT.Global.HilbertPlaces
import InverseGalois.CFT.Local.HilbertIdentities

/-!
# The product of the Hilbert symbols of a rational pair over all places

The symbol of a pair of nonzero rationals is trivial at all but finitely many finite places, so
the product of the local symbols over all places — the finite ones together with the real one —
is a well defined sign.  This file introduces that product and records the formal properties it
inherits place by place: it is symmetric, it does not see square factors, it is trivial when
either argument is one, and the product of an element against itself is its product against minus
one.

## Main results

* `InverseGalois.CFT.hilbertProduct`: the product of the local Hilbert symbols over all places.
* `InverseGalois.CFT.hilbertProduct_eq_prod_of_subset`: the product computed over an explicit
  finite set of finite places containing the support.
* `InverseGalois.CFT.hilbertProduct_mul_sq_left`, `InverseGalois.CFT.hilbertProduct_mul_sq_right`:
  square factors do not matter.
* `InverseGalois.CFT.hilbertProduct_one_left`, `InverseGalois.CFT.hilbertProduct_self`.
-/

namespace InverseGalois.CFT

open Local

/-- **The product of the Hilbert symbols of a pair of rationals over all places of the rational
field**: the real place contributes one factor and each prime contributes another. -/
noncomputable def hilbertProduct (a b : ℚ) : ℤ :=
  hilbertSymbol ((a : ℝ)) ((b : ℝ)) * ∏ᶠ p : Nat.Primes, hilbertSymbolAt p a b

/-- The product over all places is symmetric in its two arguments. -/
theorem hilbertProduct_comm (a b : ℚ) : hilbertProduct a b = hilbertProduct b a := by
  unfold hilbertProduct
  rw [hilbertSymbol_comm ((a : ℝ))]
  congr 1
  exact finprod_congr fun p => hilbertSymbolAt_comm p a b

/-- **The product over all places is computed by a finite product** as soon as one exhibits a
finite set of primes outside which the local symbol is trivial. -/
theorem hilbertProduct_eq_prod_of_subset (a b : ℚ) (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, p ∉ S → hilbertSymbolAt p a b = 1) :
    hilbertProduct a b = hilbertSymbol ((a : ℝ)) ((b : ℝ)) * ∏ p ∈ S, hilbertSymbolAt p a b := by
  unfold hilbertProduct
  congr 1
  refine finprod_eq_prod_of_mulSupport_subset _ ?_
  intro p hp
  by_contra hcon
  exact hp (hS p (by simpa using hcon))

/-- Multiplying the first argument by a nonzero square does not change the product over all
places. -/
theorem hilbertProduct_mul_sq_left (a b c : ℚ) (hc : c ≠ 0) :
    hilbertProduct (a * c ^ 2) b = hilbertProduct a b := by
  have hc' : ((c : ℝ)) ≠ 0 := by simpa using hc
  unfold hilbertProduct
  rw [show (((a * c ^ 2 : ℚ)) : ℝ) = (a : ℝ) * (c : ℝ) ^ 2 by push_cast; ring,
    hilbertSymbol_mul_sq_left _ _ _ hc']
  congr 1
  exact finprod_congr fun p => hilbertSymbolAt_mul_sq_left p a b c hc

/-- Multiplying the second argument by a nonzero square does not change the product over all
places. -/
theorem hilbertProduct_mul_sq_right (a b c : ℚ) (hc : c ≠ 0) :
    hilbertProduct a (b * c ^ 2) = hilbertProduct a b := by
  rw [hilbertProduct_comm, hilbertProduct_mul_sq_left _ _ _ hc, hilbertProduct_comm]

/-- The product over all places is trivial when the first argument is one. -/
theorem hilbertProduct_one_left (b : ℚ) : hilbertProduct 1 b = 1 := by
  unfold hilbertProduct
  have h : ∀ p : Nat.Primes, hilbertSymbolAt p 1 b = 1 := by
    intro p
    unfold hilbertSymbolAt
    rw [Rat.cast_one]
    exact hilbertSymbol_one_left _
  rw [finprod_congr h, finprod_one, mul_one, Rat.cast_one, hilbertSymbol_one_left]

/-- The product over all places is trivial when the second argument is one. -/
theorem hilbertProduct_one_right (a : ℚ) : hilbertProduct a 1 = 1 := by
  rw [hilbertProduct_comm, hilbertProduct_one_left]

/-- **The product of an element against itself is its product against minus one**, place by
place. -/
theorem hilbertProduct_self {a : ℚ} (ha : a ≠ 0) :
    hilbertProduct a a = hilbertProduct a (-1) := by
  have hr : ((a : ℝ)) ≠ 0 := by simpa using ha
  unfold hilbertProduct
  rw [hilbertSymbol_self _ hr]
  congr 1
  · norm_num
  · refine finprod_congr fun p => ?_
    have hp : ((a : ℚ_[(p : ℕ)])) ≠ 0 := by
      simpa using ha
    unfold hilbertSymbolAt
    rw [hilbertSymbol_self _ hp]
    norm_num

/-- The product over all places is a sign. -/
theorem hilbertProduct_eq_one_or {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertProduct a b = 1 ∨ hilbertProduct a b = -1 := by
  have hfin := finite_mulSupport_hilbertSymbolAt ha hb
  have h : hilbertProduct a b ^ 2 = 1 := by
    unfold hilbertProduct
    rw [mul_pow, hilbertSymbol_sq, one_mul, finprod_pow hfin]
    refine finprod_eq_one_of_forall_eq_one fun p => ?_
    exact hilbertSymbol_sq _ _
  have hu : IsUnit (hilbertProduct a b) :=
    IsUnit.of_mul_eq_one (b := hilbertProduct a b) (by rw [← sq]; exact h)
  rcases Int.isUnit_iff.1 hu with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

end InverseGalois.CFT
