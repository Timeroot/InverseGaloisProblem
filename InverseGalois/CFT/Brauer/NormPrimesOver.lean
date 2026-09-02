/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.NormFactors
import InverseGalois.CFT.Brauer.NormPlaceValue

/-!
# The norm of an algebraic integer modulo a rational prime, place by place

The ring of integers of a number field is a finitely generated torsion free module over the ring of
integers of the rationals, which is a principal ideal ring, so it is free of rank the degree of the
field.  Reducing modulo a rational prime and splitting by the Chinese remainder theorem therefore
expresses the reduction of the norm of an algebraic integer as the product, over the places of the
number field above that prime, of the norms of its reductions modulo the corresponding ramified
powers.

The places above a rational prime are exactly the primes of the ring of integers lying over it, and
a place lies over a rational prime precisely when that prime is the one below the place.  Matching
the two descriptions turns the product over the prime factors of the pushforward into a product
over the fibre of the map sending a place to the rational prime below it, which is the shape in
which the invariants of a class in the Brauer group are grouped.

## Main results

* `InverseGalois.CFT.primeUnder_eq_iff_liesOver`: a place of a number field lies over a rational
  prime exactly when that prime is the one below it.
* `InverseGalois.CFT.placesOverEquiv`: **the places above a rational prime match the primes over
  it.**
* `InverseGalois.CFT.mk_norm_eq_prod_norm_primesOver`: **the norm of an algebraic integer reduces
  modulo a rational prime to the product, over the primes of the number field over it, of the norms
  of the reductions modulo the corresponding ramified powers.**
* `InverseGalois.CFT.finprod_norm_places_eq_mk_norm`: **the same, as a product over the places of
  the number field above the rational prime.**

## Tags

number field, ring of integers, norm, Chinese remainder theorem, ramification, residue field,
places, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField Ideal UniqueFactorizationMonoid

section PrimesOver

variable {k : Type} [Field k] [NumberField k]

/-- A place of a number field lies over a rational prime exactly when that prime is the one below
it. -/
theorem primeUnder_eq_iff_liesOver (P : HeightOneSpectrum (𝓞 ℚ))
    (v : HeightOneSpectrum (𝓞 k)) :
    primeUnder (𝓞 ℚ) v = P ↔ v.asIdeal.LiesOver P.asIdeal := by
  rw [Ideal.liesOver_iff, HeightOneSpectrum.ext_iff, primeUnder_asIdeal]
  exact eq_comm

open scoped Classical in
/-- **The places of a number field above a rational prime match the primes over it.** -/
noncomputable def placesOverEquiv (P : HeightOneSpectrum (𝓞 ℚ)) :
    {v : HeightOneSpectrum (𝓞 k) // primeUnder (𝓞 ℚ) v = P} ≃
      ↥(primesOverFinset P.asIdeal (𝓞 k)) where
  toFun v := ⟨v.1.asIdeal, by
    haveI : P.asIdeal.IsMaximal := HeightOneSpectrum.isMaximal P
    exact (mem_primesOverFinset_iff P.ne_bot _).mpr
      ⟨v.1.isPrime, (primeUnder_eq_iff_liesOver P v.1).mp v.2⟩⟩
  invFun Q := by
    haveI : P.asIdeal.IsMaximal := HeightOneSpectrum.isMaximal P
    have hQ := (mem_primesOverFinset_iff P.ne_bot _).mp Q.2
    exact ⟨⟨Q.1, hQ.1, ne_bot_of_mem_primesOver P.ne_bot hQ⟩,
      (primeUnder_eq_iff_liesOver P _).mpr hQ.2⟩
  left_inv v := by ext; rfl
  right_inv Q := by ext; rfl

open scoped Classical in
/-- **The norm of an algebraic integer reduces modulo a rational prime to the product, over the
primes of the ring of integers over it, of the norms of the reductions modulo the corresponding
ramified powers.**  The ring of integers is free over the integers of the rationals, of rank the
degree of the field, which is the dimension of the reduction over the residue field. -/
theorem mk_norm_eq_prod_norm_primesOver (P : HeightOneSpectrum (𝓞 ℚ)) (b : 𝓞 k) :
    Ideal.Quotient.mk P.asIdeal (Algebra.norm (𝓞 ℚ) b)
      = ∏ Q : (factors (P.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 k)))).toFinset,
          Algebra.norm (𝓞 ℚ ⧸ P.asIdeal) (Ideal.Quotient.mk
            ((Q : Ideal (𝓞 k)) ^ ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 k)) P.asIdeal Q) b) := by
  haveI : P.asIdeal.IsMaximal := HeightOneSpectrum.isMaximal P
  haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm
      Rat.ringOfIntegersEquiv.symm.surjective
  haveI : Module.Free (𝓞 ℚ) (𝓞 k) :=
    Module.free_of_finite_type_torsion_free' (R := 𝓞 ℚ) (M := 𝓞 k)
  have hmap : P.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 k)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (𝓞 ℚ) (𝓞 k))
      = finrank (𝓞 ℚ ⧸ P.asIdeal) (𝓞 k ⧸ P.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 k))) := by
    rw [Ideal.finrank_quotient_map (K := ℚ) (L := k) _,
      Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 ℚ) ℚ (𝓞 k) k]
    exact (finrank_eq_card_chooseBasisIndex (R := 𝓞 ℚ) (M := 𝓞 k)).symm
  exact mk_norm_eq_prod_norm_factors P.asIdeal hmap (Module.Free.chooseBasis (𝓞 ℚ) (𝓞 k)) hcard b

/-- **The norm of an algebraic integer reduces modulo a rational prime to the product, over the
places of the number field above it, of the norms of the reductions modulo the corresponding
ramified powers.**  The places outside the fibre contribute nothing. -/
theorem finprod_norm_places_eq_mk_norm (P : HeightOneSpectrum (𝓞 ℚ)) (b : 𝓞 k) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P}
          (fun u => Algebra.norm (𝓞 ℚ ⧸ P.asIdeal) (Ideal.Quotient.mk
            (u.asIdeal ^ ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 k)) P.asIdeal u.asIdeal) b)) v
      = Ideal.Quotient.mk P.asIdeal (Algebra.norm (𝓞 ℚ) b) := by
  classical
  letI hft : Fintype {v : HeightOneSpectrum (𝓞 k) // primeUnder (𝓞 ℚ) v = P} :=
    Fintype.ofEquiv _ (placesOverEquiv P).symm
  letI : Fintype ↑({u : HeightOneSpectrum (𝓞 k) | primeUnder (𝓞 ℚ) u = P}) := hft
  rw [← finprod_mem_def, ← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype,
    mk_norm_eq_prod_norm_primesOver P b]
  exact Fintype.prod_equiv (placesOverEquiv P) _ _ fun v => rfl

end PrimesOver

end InverseGalois.CFT
