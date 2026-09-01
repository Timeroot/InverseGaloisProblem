/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.RamifiedCyclotomicPlace
import InverseGalois.CFT.Local.AdicUnits
import InverseGalois.CFT.Local.RatResidueDegree

/-!
# A rational prime is a uniformiser of its completion

The ramification index of a finite place of the rationals over the rational prime below it is at
most the degree of the rationals over themselves, and it is positive, so it is one.  The valuation
of a rational prime at a place above it is the exponential of minus the ramification index, so the
prime itself is a uniformiser of the completion: its valuation is one step below one, and the
residue characteristic of the completion comes with exponent one.

That exponent is what the invariant of a cyclic algebra measures.  The valuation of a unit, divided
by the generator `1` of the value group of a completion, is the logarithm of its valuation, so it
is minus one at a uniformiser and one at the reciprocal of a uniformiser — which is the shape in
which the value of the tame norm residue symbol is stated.

## Main results

* `InverseGalois.CFT.ramificationIdx_rat_eq_one`: **a finite place of the rationals is unramified
  over the rational prime below it.**
* `InverseGalois.CFT.valued_natCast_adicCompletion_rat`: **a rational prime is a uniformiser of the
  completion of the rationals at a place containing it.**
* `InverseGalois.CFT.hasResidueChar_adicCompletion_rat_of_mem`: **the completion of the rationals at
  a place containing a rational prime has that prime as its residue characteristic, with exponent
  one.**
* `InverseGalois.CFT.unitValDiv_inv_eq_one_of_valued_eq_exp_neg_one`: the reciprocal of a
  uniformiser has divided valuation one.

## Tags

number field, finite place, ramification index, uniformiser, adic completion, residue
characteristic, class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped WithZero

/-! ### The ramification index of a finite place of the rationals -/

/-- **A finite place of the rationals is unramified over the rational prime below it.**  The
ramification index of a place is at most the degree of the field over the rationals and is
positive, and here that degree is one. -/
theorem ramificationIdx_rat_eq_one {q : ℕ} (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    [v.asIdeal.LiesOver (Ideal.span {(q : ℤ)})] :
    Ideal.ramificationIdx (algebraMap ℤ (𝓞 ℚ)) (Ideal.span {(q : ℤ)}) v.asIdeal = 1 := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI := isMaximal_span_prime hq
  have hle := Ideal.ramificationIdx_le_finrank (R := ℤ) (S := 𝓞 ℚ) (K := ℚ) (L := ℚ)
    (p := Ideal.span {(q : ℤ)}) v.asIdeal
  have hne := ramificationIdx_span_ne_zero (p := q) (K := ℚ) v
  rw [Module.finrank_self] at hle
  omega

/-! ### A rational prime is a uniformiser -/

/-- **A rational prime is a uniformiser of the completion of the rationals at a place containing
it.**  Its valuation there is the exponential of minus the ramification index, which is one. -/
theorem valued_natCast_adicCompletion_rat {q : ℕ} (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    [v.asIdeal.LiesOver (Ideal.span {(q : ℤ)})] :
    Valued.v ((q : ℕ) : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  have hval : Valued.v ((q : ℕ) : v.adicCompletion ℚ) = v.valuation ℚ ((q : ℕ) : ℚ) := by
    rw [← map_natCast (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ)) q,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
    norm_cast
  rw [hval, valuation_natCast_eq_exp_neg_ramificationIdx hq v, ramificationIdx_rat_eq_one hq v,
    Nat.cast_one]

/-- **The completion of the rationals at a place over a rational prime has that prime as its
residue characteristic, with exponent one.** -/
theorem hasResidueChar_adicCompletion_rat {q : ℕ} (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    [v.asIdeal.LiesOver (Ideal.span {(q : ℤ)})] : HasResidueChar (v.adicCompletion ℚ) q 1 :=
  ⟨hq, one_pos, by rw [valued_natCast_adicCompletion_rat hq v, Nat.cast_one]⟩

/-- **The completion of the rationals at a place containing a rational prime has that prime as its
residue characteristic, with exponent one.**  A place containing a rational prime lies over it. -/
theorem hasResidueChar_adicCompletion_rat_of_mem {q : ℕ} (hq : q.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    HasResidueChar (v.adicCompletion ℚ) q 1 :=
  haveI := liesOver_span_of_natCast_mem hq v hv
  hasResidueChar_adicCompletion_rat hq v

/-! ### The divided valuation of a uniformiser -/

section Uniformiser

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-- **A uniformiser has divided valuation minus one** when the valuation of the field is onto: the
generator of the value group is then one, and dividing by it leaves the logarithm alone. -/
theorem unitValDiv_eq_neg_one_of_valued_eq_exp_neg_one
    (h : Function.Surjective (Valued.v : A → ℤᵐ⁰)) {u : Aˣ}
    (hu : Valued.v ((u : A)) = WithZero.exp (-1 : ℤ)) :
    unitValDiv (isUnitValGen_one h) (Additive.ofMul u) = -1 := by
  rw [unitValDiv_apply, unitVal_apply, hu, WithZero.log_exp, Int.ediv_one]

/-- **The reciprocal of a uniformiser has divided valuation one**, which is the normalisation in
which the value of the tame norm residue symbol is stated. -/
theorem unitValDiv_inv_eq_one_of_valued_eq_exp_neg_one
    (h : Function.Surjective (Valued.v : A → ℤᵐ⁰)) {u : Aˣ}
    (hu : Valued.v ((u : A)) = WithZero.exp (-1 : ℤ)) :
    unitValDiv (isUnitValGen_one h) (Additive.ofMul u⁻¹) = 1 := by
  have hneg : Additive.ofMul u⁻¹ = -(Additive.ofMul u) := rfl
  rw [hneg, map_neg, unitValDiv_eq_neg_one_of_valued_eq_exp_neg_one h hu, neg_neg]

end Uniformiser

end InverseGalois.CFT
