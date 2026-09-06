/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.NormReduction

/-!
# The norm modulo a prime of the base, factor by factor

The reduction of an extension of Dedekind domains modulo a maximal ideal of the base splits, by
the Chinese remainder theorem, as the product of the reductions modulo the powers of the primes
lying over it to which they ramify.  That splitting is an isomorphism of algebras over the residue
field of the base, so the norm of an element reduces to the product over those primes of the norms
of the reductions.  Combined with the reduction of the norm modulo a maximal ideal this expresses
the reduction of a global norm as a product of local contributions.

A second, unrelated computation records the shape a norm of finite fields takes as a power.  The
norm from a finite field to a subfield is the power by the quotient of the two orders of the
multiplicative groups, so raising to the power the order of the big multiplicative group divided by
a divisor `N` of the order of the small one is the same as taking the norm and then raising to the
power the order of the small multiplicative group divided by `N`.  This is what converts a power
residue symbol computed in a large residue field into one computed in the prime field.

## Main results

* `InverseGalois.CFT.mk_norm_eq_prod_norm_factors`: **the norm of an element reduces modulo a
  maximal ideal of the base to the product, over the primes lying over it, of the norms of the
  reductions modulo the corresponding ramified powers.**
* `InverseGalois.CFT.pow_natCard_sub_one_div_eq`: **raising an element of a finite field to the
  power the order of its multiplicative group divided by `N` is the norm to a subfield, raised to
  the power the order of the smaller multiplicative group divided by `N`.**

## Tags

norm, Dedekind domain, Chinese remainder theorem, ramification, residue field, finite field
-/

namespace InverseGalois.CFT

open Module Ideal UniqueFactorizationMonoid

/-! ### The norm modulo a maximal ideal, factor by factor -/

section Factors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDedekindDomain S]
  (p : Ideal R) [p.IsMaximal] [Module.Finite R S]

attribute [local instance] Ideal.Quotient.field

open scoped Classical in
/-- **The Chinese remainder theorem for the reduction of an extension of Dedekind domains modulo a
maximal ideal of the base**, as an isomorphism of algebras over the residue field of the base. -/
noncomputable def piQuotientAlgEquiv (hp : Ideal.map (algebraMap R S) p ≠ ⊥) :
    (S ⧸ Ideal.map (algebraMap R S) p) ≃ₐ[R ⧸ p]
      ∀ P : (factors (Ideal.map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P :=
  AlgEquiv.ofLinearEquiv (Ideal.Factors.piQuotientLinearEquiv S p hp)
    (map_one (Ideal.Factors.piQuotientEquiv p hp)) (map_mul (Ideal.Factors.piQuotientEquiv p hp))

omit [p.IsMaximal] [Module.Finite R S] in
open scoped Classical in
/-- The Chinese remainder isomorphism sends the reduction of an element to its reductions modulo
the individual ramified powers. -/
theorem piQuotientAlgEquiv_mk (hp : Ideal.map (algebraMap R S) p ≠ ⊥) (a : S) :
    piQuotientAlgEquiv p hp (Ideal.Quotient.mk _ a) = fun _ => Ideal.Quotient.mk _ a := rfl

open scoped Classical in
/-- **The norm of an element reduces modulo a maximal ideal of the base to the product, over the
primes lying over it, of the norms of the reductions modulo the corresponding ramified powers**,
whenever the reduction of the extension has the dimension the rank predicts. -/
theorem mk_norm_eq_prod_norm_factors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hp : Ideal.map (algebraMap R S) p ≠ ⊥) (b : Basis ι R S)
    (h : Fintype.card ι = finrank (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p)) (a : S) :
    Ideal.Quotient.mk p (Algebra.norm R a)
      = ∏ P : (factors (Ideal.map (algebraMap R S) p)).toFinset,
          Algebra.norm (R ⧸ p) (Ideal.Quotient.mk
            ((P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) a) := by
  haveI : ∀ P : (factors (Ideal.map (algebraMap R S) p)).toFinset,
      Module.Free (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) :=
    fun _ => Module.Free.of_divisionRing _ _
  rw [mk_norm_eq_norm_mk p b h a, ← Algebra.norm_eq_of_algEquiv (piQuotientAlgEquiv p hp),
    piQuotientAlgEquiv_mk]
  exact norm_pi_eq_prod _ _

end Factors

/-! ### Powers and norms of finite fields -/

section FiniteFields

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [Finite K]

/-- The order of the multiplicative group of a subfield of a finite field divides the order of the
multiplicative group of the field. -/
theorem natCard_sub_one_dvd : Nat.card F - 1 ∣ Nat.card K - 1 := by
  have : Finite F := Finite.of_injective _ (algebraMap F K).injective
  have := Fintype.ofFinite F
  have := Fintype.ofFinite K
  have hcard : Nat.card K = Nat.card F ^ finrank F K := by
    simpa [Nat.card_eq_fintype_card] using Module.card_eq_pow_finrank (K := F) (V := K)
  rw [hcard]
  simpa using Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 (finrank F K)

variable {F K}

/-- **Raising an element of a finite field to the power the order of its multiplicative group
divided by `N` is the norm to a subfield, raised to the power the order of the smaller
multiplicative group divided by `N`**, for any nonzero `N` dividing the latter order. -/
theorem pow_natCard_sub_one_div_eq {N : ℕ} (hN : N ≠ 0) (hNF : N ∣ Nat.card F - 1) (x : K) :
    x ^ ((Nat.card K - 1) / N) = algebraMap F K (Algebra.norm F x ^ ((Nat.card F - 1) / N)) := by
  have : Finite F := Finite.of_injective _ (algebraMap F K).injective
  have hF1 : Nat.card F - 1 ≠ 0 := by
    have := Finite.one_lt_card (α := F)
    omega
  obtain ⟨t, ht⟩ := hNF
  obtain ⟨s, hs⟩ := natCard_sub_one_dvd F K
  have h1 : (Nat.card K - 1) / N = t * s := by
    rw [hs, ht, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN)]
  have h2 : (Nat.card F - 1) / N = t := by
    rw [ht, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN)]
  have h3 : (Nat.card K - 1) / (Nat.card F - 1) = s := by
    rw [hs, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hF1)]
  rw [h1, h2, map_pow, FiniteField.algebraMap_norm_eq_pow, h3, ← pow_mul, mul_comm s t]

end FiniteFields

end InverseGalois.CFT
