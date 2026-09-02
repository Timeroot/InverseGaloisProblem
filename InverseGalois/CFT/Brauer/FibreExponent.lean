/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.NormPrimesOver

/-!
# The exponents above one rational prime add up

The invariant of a cyclic algebra at a place above the prime of the conductor is named by an
exponent: the coefficient raised to the number of residues of the place less one, divided by the
degree, is congruent there to that power of a root of unity, and the root of unity is represented
in the residue field by a natural number.  Comparing the places of a number field above one
rational prime with the prime itself therefore means comparing those exponents.

The comparison is a computation with norms of residue fields.  Raising an element of a residue
field to the number of its elements less one, divided by the degree, is the same as taking the norm
to the residue field of the rational prime below and raising the result to the number of elements
there less one, divided by the degree.  So each place contributes the norm of the reduction of the
coefficient, raised to a power computed once and for all in the residue field of the rational
prime, and the exponent of the place is read off there.  When the rational prime is unramified,
reduction modulo a place above it is reduction modulo the ramified power to which the Chinese
remainder theorem splits the norm, so the product of the contributions over the fibre is the
reduction of the norm of the coefficient.

Finally, the natural number representing the root of unity has order exactly the degree in the
residue field of the rational prime, so an equality of its powers is a congruence of the exponents:
the exponents of the places above a rational prime add up, modulo the degree, to the exponent of
the prime itself.

## Main results

* `InverseGalois.CFT.quotPowRamAlgEquiv`: at an unramified prime, reduction modulo a place is
  reduction modulo the ramified power, as an isomorphism of algebras over the residue field below.
* `InverseGalois.CFT.norm_mk_pow_ramificationIdx_eq`: hence the two norms agree.
* `InverseGalois.CFT.norm_mk_pow_eq_mk_natCast_pow`: **the norm of the reduction of an integer at a
  place, raised to the number of residues of the rational prime below less one over the degree, is
  the power by the exponent naming the place of the natural number representing the root of
  unity.**
* `InverseGalois.CFT.mk_norm_pow_eq_mk_natCast_pow`: **the reduction of the norm of an integer,
  raised to that power, is the power of the natural number by the sum of the exponents over the
  places above the prime.**
* `InverseGalois.CFT.natCast_finsum_eq_natCast_of_residue`: **the exponents above a rational prime
  add up, modulo the degree, to the exponent of the prime.**

## Tags

number field, place, residue field, norm, ramification, power residue symbol, reciprocity,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField Ideal

attribute [local instance] Ideal.Quotient.field

section FibreExponent

variable {k : Type} [Field k] [NumberField k]

/-- **At an unramified prime, reduction modulo a place is reduction modulo the ramified power**, as
an isomorphism of algebras over the residue field of the prime below. -/
noncomputable def quotPowRamAlgEquiv (P : HeightOneSpectrum (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 k))
    [v.asIdeal.LiesOver P.asIdeal]
    (he : ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 k)) P.asIdeal v.asIdeal = 1) :
    (𝓞 k ⧸ v.asIdeal ^ ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 k)) P.asIdeal v.asIdeal)
      ≃ₐ[𝓞 ℚ ⧸ P.asIdeal] (𝓞 k ⧸ v.asIdeal) :=
  AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq (by rw [he, pow_one]))
    (fun x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)

/-- At an unramified prime the norm of the reduction of an integer modulo a place agrees with the
norm of its reduction modulo the ramified power. -/
theorem norm_mk_pow_ramificationIdx_eq (P : HeightOneSpectrum (𝓞 ℚ))
    (v : HeightOneSpectrum (𝓞 k)) [v.asIdeal.LiesOver P.asIdeal]
    (he : ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 k)) P.asIdeal v.asIdeal = 1) (b : 𝓞 k) :
    Algebra.norm (𝓞 ℚ ⧸ P.asIdeal) (Ideal.Quotient.mk
        (v.asIdeal ^ ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 k)) P.asIdeal v.asIdeal) b)
      = Algebra.norm (𝓞 ℚ ⧸ P.asIdeal) (Ideal.Quotient.mk v.asIdeal b) := by
  have hb : quotPowRamAlgEquiv P v he (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk v.asIdeal b := rfl
  rw [← hb, Algebra.norm_eq_of_algEquiv]

/-- **The norm of the reduction of an integer at a place, raised to the number of residues of the
rational prime below less one over the degree, is the power by the exponent naming the place of the
natural number representing the root of unity.**  Raising to that power in the residue field below
is, after the map to the residue field of the place, raising to the number of residues there less
one over the degree, so the naming congruence at the place transports along an injection. -/
theorem norm_mk_pow_eq_mk_natCast_pow (P : HeightOneSpectrum (𝓞 ℚ))
    (v : HeightOneSpectrum (𝓞 k)) [v.asIdeal.LiesOver P.asIdeal] {N c j : ℕ} {b : 𝓞 k}
    (hN : N ≠ 0) (hNP : N ∣ Nat.card (𝓞 ℚ ⧸ P.asIdeal) - 1)
    (hmk : Ideal.Quotient.mk v.asIdeal (b ^ ((Nat.card (𝓞 k ⧸ v.asIdeal) - 1) / N))
      = Ideal.Quotient.mk v.asIdeal (((c ^ j : ℕ) : 𝓞 k))) :
    Algebra.norm (𝓞 ℚ ⧸ P.asIdeal) (Ideal.Quotient.mk v.asIdeal b)
          ^ ((Nat.card (𝓞 ℚ ⧸ P.asIdeal) - 1) / N)
      = Ideal.Quotient.mk P.asIdeal ((c : ℕ) : 𝓞 ℚ) ^ j := by
  haveI : P.asIdeal.IsMaximal := HeightOneSpectrum.isMaximal P
  haveI : v.asIdeal.IsMaximal := HeightOneSpectrum.isMaximal v
  refine (algebraMap (𝓞 ℚ ⧸ P.asIdeal) (𝓞 k ⧸ v.asIdeal)).injective ?_
  rw [← pow_natCard_sub_one_div_eq hN hNP, ← map_pow, hmk, map_pow]
  push_cast
  rw [map_pow, Ideal.Quotient.algebraMap_mk_of_liesOver, map_natCast]
  simp

/-- **The reduction of the norm of an integer modulo an unramified rational prime, raised to the
number of residues there less one over the degree, is the power of the natural number representing
the root of unity by the sum of the exponents over the places above the prime.**  The Chinese
remainder splitting of the norm is a product over the fibre, and each factor is named by the
exponent of its place. -/
theorem mk_norm_pow_eq_mk_natCast_pow (P : HeightOneSpectrum (𝓞 ℚ)) {b : 𝓞 k} {N c : ℕ}
    (hN : N ≠ 0) (hNP : N ∣ Nat.card (𝓞 ℚ ⧸ P.asIdeal) - 1)
    (j : HeightOneSpectrum (𝓞 k) → ℕ)
    (hunram : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 k)) P.asIdeal v.asIdeal = 1)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      Ideal.Quotient.mk v.asIdeal (b ^ ((Nat.card (𝓞 k ⧸ v.asIdeal) - 1) / N))
        = Ideal.Quotient.mk v.asIdeal (((c ^ j v : ℕ) : 𝓞 k))) :
    Ideal.Quotient.mk P.asIdeal (Algebra.norm (𝓞 ℚ) b)
          ^ ((Nat.card (𝓞 ℚ ⧸ P.asIdeal) - 1) / N)
      = Ideal.Quotient.mk P.asIdeal ((c : ℕ) : 𝓞 ℚ)
          ^ (∑ᶠ v ∈ {u : HeightOneSpectrum (𝓞 k) | primeUnder (𝓞 ℚ) u = P}, j v) := by
  classical
  letI hft : Fintype {v : HeightOneSpectrum (𝓞 k) // primeUnder (𝓞 ℚ) v = P} :=
    Fintype.ofEquiv _ (placesOverEquiv P).symm
  letI : Fintype ↑({u : HeightOneSpectrum (𝓞 k) | primeUnder (𝓞 ℚ) u = P}) := hft
  rw [← finprod_norm_places_eq_mk_norm P b, ← finprod_mem_def,
    ← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype, ← Finset.prod_pow,
    ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun w _ => ?_
  haveI : (w : HeightOneSpectrum (𝓞 k)).asIdeal.LiesOver P.asIdeal :=
    (primeUnder_eq_iff_liesOver P _).mp w.2
  rw [norm_mk_pow_ramificationIdx_eq P _ (hunram _ w.2) b]
  exact norm_mk_pow_eq_mk_natCast_pow P _ hN hNP (hres _ w.2)

/-- **The exponents naming the places above an unramified rational prime add up, modulo the degree,
to the exponent naming the prime.**  The natural number representing the root of unity has order
the degree in the residue field of the prime, so an equality of its powers is a congruence of the
exponents. -/
theorem natCast_finsum_eq_natCast_of_residue (P : HeightOneSpectrum (𝓞 ℚ)) {b : 𝓞 k}
    {N c j' : ℕ} (hN : N ≠ 0) (hNP : N ∣ Nat.card (𝓞 ℚ ⧸ P.asIdeal) - 1)
    (hord : orderOf (Ideal.Quotient.mk P.asIdeal ((c : ℕ) : 𝓞 ℚ)) = N)
    (j : HeightOneSpectrum (𝓞 k) → ℕ)
    (hunram : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 k)) P.asIdeal v.asIdeal = 1)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      Ideal.Quotient.mk v.asIdeal (b ^ ((Nat.card (𝓞 k ⧸ v.asIdeal) - 1) / N))
        = Ideal.Quotient.mk v.asIdeal (((c ^ j v : ℕ) : 𝓞 k)))
    (hres' : Ideal.Quotient.mk P.asIdeal
        (Algebra.norm (𝓞 ℚ) b ^ ((Nat.card (𝓞 ℚ ⧸ P.asIdeal) - 1) / N))
      = Ideal.Quotient.mk P.asIdeal (((c ^ j' : ℕ) : 𝓞 ℚ))) :
    ((∑ᶠ v ∈ {u : HeightOneSpectrum (𝓞 k) | primeUnder (𝓞 ℚ) u = P}, j v : ℕ) : ZMod N)
      = (j' : ZMod N) := by
  have hx : Ideal.Quotient.mk P.asIdeal ((c : ℕ) : 𝓞 ℚ)
        ^ (∑ᶠ v ∈ {u : HeightOneSpectrum (𝓞 k) | primeUnder (𝓞 ℚ) u = P}, j v)
      = Ideal.Quotient.mk P.asIdeal ((c : ℕ) : 𝓞 ℚ) ^ j' := by
    rw [← mk_norm_pow_eq_mk_natCast_pow P hN hNP j hunram hres, ← map_pow, hres']
    push_cast
    rw [map_pow]
  have hfin : IsOfFinOrder (Ideal.Quotient.mk P.asIdeal ((c : ℕ) : 𝓞 ℚ)) :=
    orderOf_pos_iff.mp (by rw [hord]; exact Nat.pos_of_ne_zero hN)
  have hmod := hfin.pow_eq_pow_iff_modEq.mp hx
  rw [hord] at hmod
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

end FibreExponent

end InverseGalois.CFT
