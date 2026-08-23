import Mathlib
import InverseGalois.CFT.Global.LocalSquare
import InverseGalois.CFT.Local.RamifiedNormForm

/-!
# The symbol at an odd place against a unit depends only on a parity

Let `p` be an odd prime and let `a` be an integer prime to `p`.  Writing an arbitrary nonzero
`p`-adic number as a power of the uniformiser times a unit, the even part of that power is a
square and so does not affect the Hilbert symbol against `a`.  What is left is either a pair of
units, whose symbol is trivial, or the ramified computation of the norm form, whose value is the
quadratic character of the residue of `a`.  So the symbol takes only the two values `1` and the
Legendre symbol of `a`, selected by the parity of the valuation of the second argument.

## Main results

* `InverseGalois.CFT.hilbertSymbol_unit_eq`: the local statement over the field of `p`-adic
  numbers, for a unit of the ring of `p`-adic integers against an arbitrary nonzero element.
* `InverseGalois.CFT.hilbertSymbolAt_odd_eq`: the symbol at an odd place of an integer prime to
  `p` against a nonzero rational is `1` or the Legendre symbol, according to the parity of the
  valuation of the second argument.
* `InverseGalois.CFT.hilbertSymbolAt_odd_of_even_valuation`,
  `InverseGalois.CFT.hilbertSymbolAt_odd_of_odd_valuation`: the two branches, separately.
-/

namespace InverseGalois.CFT

open Local

/-- **The symbol of a `p`-adic unit against an arbitrary nonzero `p`-adic number**, for `p` odd:
it is trivial when the valuation of the second argument is even, and the quadratic character of
the residue of the unit when that valuation is odd. -/
theorem hilbertSymbol_unit_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u : ℤ_[p]} (hu : IsUnit u)
    {y : ℚ_[p]} (hy : y ≠ 0) :
    hilbertSymbol ((u : ℚ_[p])) y =
      if Even y.valuation then 1 else quadraticChar (ZMod p) (PadicInt.toZMod u) := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  have hev : Even (0 : ℤ) := ⟨0, (add_zero 0).symm⟩
  obtain ⟨n, v, hv, rfl⟩ := exists_unit_mul_zpow hy
  have hvne : ((v : ℚ_[p])) ≠ 0 := PadicInt.coe_ne_zero.mpr hv.ne_zero
  have hval : ((p : ℚ_[p]) ^ n * (v : ℚ_[p])).valuation = n := by
    rw [Padic.valuation_mul (zpow_ne_zero _ hp0) hvne, Padic.valuation_zpow, Padic.valuation_p,
      valuation_coe_eq_zero hv]
    ring
  rw [hval]
  by_cases hn : Even n
  · rw [if_pos hn]
    refine hilbertSymbol_of_even_valuations hp (PadicInt.coe_ne_zero.mpr hu.ne_zero)
      (mul_ne_zero (zpow_ne_zero _ hp0) hvne) ?_ ?_
    · rw [valuation_coe_eq_zero hu]; exact hev
    · rw [hval]; exact hn
  · rw [if_neg hn]
    obtain ⟨m, hm⟩ := Int.not_even_iff_odd.mp hn
    have hm2 : n = m * 2 + 1 := by omega
    have hA : (p : ℚ_[p]) ^ n * (v : ℚ_[p])
        = ((p : ℚ_[p]) * (v : ℚ_[p])) * ((p : ℚ_[p]) ^ m) ^ (2 : ℕ) := by
      rw [hm2, zpow_add₀ hp0, zpow_one, zpow_mul, ← zpow_natCast ((p : ℚ_[p]) ^ m) 2]
      push_cast
      ring
    rw [hA, hilbertSymbol_mul_sq_right _ _ _ (zpow_ne_zero _ hp0)]
    have h := hilbertSymbol_ramified_eq (p := p) hp hv (n := 0) hu
    rw [zpow_zero, one_mul, if_pos hev, mul_one] at h
    exact h

/-- **The symbol at an odd place of an integer prime to `p` against a nonzero rational** is
governed by the parity of the `p`-adic valuation of the second argument: it is trivial in the
even case and the Legendre symbol of the first argument in the odd case. -/
theorem hilbertSymbolAt_odd_eq {p : Nat.Primes} (hp : (p : ℕ) ≠ 2) {a : ℤ}
    (ha : ¬ ((p : ℕ) : ℤ) ∣ a) {y : ℚ} (hy : y ≠ 0) :
    hilbertSymbolAt p (a : ℚ) y =
      if Even ((y : ℚ_[(p : ℕ)])).valuation then 1 else legendreSym (p : ℕ) a := by
  have hu : IsUnit ((a : ℤ_[(p : ℕ)])) := isUnit_intCast_of_not_dvd ha
  have hyne : ((y : ℚ_[(p : ℕ)])) ≠ 0 := by
    simpa using hy
  unfold hilbertSymbolAt
  rw [show ((a : ℚ) : ℚ_[(p : ℕ)]) = ((a : ℤ_[(p : ℕ)]) : ℚ_[(p : ℕ)]) by
        rw [PadicInt.coe_intCast]; push_cast; ring,
    hilbertSymbol_unit_eq hp hu hyne, legendreSym_eq_quadraticChar_toZMod]

/-- At an odd place, an integer prime to `p` has trivial symbol against any nonzero rational of
even `p`-adic valuation. -/
theorem hilbertSymbolAt_odd_of_even_valuation {p : Nat.Primes} (hp : (p : ℕ) ≠ 2) {a : ℤ}
    (ha : ¬ ((p : ℕ) : ℤ) ∣ a) {y : ℚ} (hy : y ≠ 0)
    (hev : Even ((y : ℚ_[(p : ℕ)])).valuation) : hilbertSymbolAt p (a : ℚ) y = 1 := by
  rw [hilbertSymbolAt_odd_eq hp ha hy, if_pos hev]

/-- At an odd place, the symbol of an integer prime to `p` against a nonzero rational of odd
`p`-adic valuation is the Legendre symbol of the integer. -/
theorem hilbertSymbolAt_odd_of_odd_valuation {p : Nat.Primes} (hp : (p : ℕ) ≠ 2) {a : ℤ}
    (ha : ¬ ((p : ℕ) : ℤ) ∣ a) {y : ℚ} (hy : y ≠ 0)
    (hev : ¬ Even ((y : ℚ_[(p : ℕ)])).valuation) :
    hilbertSymbolAt p (a : ℚ) y = legendreSym (p : ℕ) a := by
  rw [hilbertSymbolAt_odd_eq hp ha hy, if_neg hev]

end InverseGalois.CFT
