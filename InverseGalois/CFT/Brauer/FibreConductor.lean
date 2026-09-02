/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.FibreExponent
import InverseGalois.CFT.Brauer.FibreInvariant

/-!
# The invariants above the prime of the conductor multiply to the rational one

At a place above the prime whose roots of unity generate the splitting field, the invariant of a
cyclic algebra is named by an exponent: the coefficient, raised to the complement of the number of
nonzero residues for the prescribed order, is congruent to a power of a fixed generator of the
residues of the rational prime, and the invariant is the class of that power.  The same holds at
the rational prime itself, for the norm of the coefficient.

The two are compared by the reduction of the norm.  Reducing the coefficient modulo each place
above the rational prime and multiplying the norms of the reductions gives the reduction of the
norm, so the generator raised to the sum of the exponents above the prime agrees with the generator
raised to the exponent at the prime; since the generator has exactly the prescribed order, the
exponents above the prime add up to the one below it, modulo that order.  Exponentiating the
additive character then turns the congruence into the equality of the product of the invariants
above the prime with the invariant at the prime.

## Main results

* `InverseGalois.CFT.finprod_placeInvariant_fibre_eq_of_residue`: **the product of the invariants
  over the places above a rational prime is the invariant at that prime**, as soon as each of them
  is named by the exponent of a residue congruence and the prime is unramified in the number field.

## Tags

number field, Brauer group, local invariant, total invariant, norm, residue field, conductor,
reciprocity, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField Ideal

section FibreConductor

variable {k : Type} [Field k] [NumberField k]

/-- **The product of the invariants over the places of a number field above a rational prime is the
invariant at that prime**, as soon as each of them is named by the exponent of a residue congruence
against a generator of order the prescribed one, and the prime is unramified in the number field.
The reduction of the norm of the coefficient is the product of the norms of its reductions, so the
exponents above the prime add up to the one below it modulo the order of the generator, and the
additive character carries that congruence to the equality of the invariants. -/
theorem finprod_placeInvariant_fibre_eq_of_residue {N : ℕ} [NeZero N] (X : BrauerGroup.{0, 0} k)
    (Z : BrauerGroup.{0, 0} ℚ) (P : HeightOneSpectrum (𝓞 ℚ)) {b : 𝓞 k} {c j' : ℕ}
    (hNP : N ∣ Nat.card (𝓞 ℚ ⧸ P.asIdeal) - 1)
    (hord : orderOf (Ideal.Quotient.mk P.asIdeal ((c : ℕ) : 𝓞 ℚ)) = N)
    (j : HeightOneSpectrum (𝓞 k) → ℕ)
    (hunram : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      ramificationIdx (algebraMap (𝓞 ℚ) (𝓞 k)) P.asIdeal v.asIdeal = 1)
    (hres : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      Ideal.Quotient.mk v.asIdeal (b ^ ((Nat.card (𝓞 k ⧸ v.asIdeal) - 1) / N))
        = Ideal.Quotient.mk v.asIdeal (((c ^ j v : ℕ) : 𝓞 k)))
    (hres' : Ideal.Quotient.mk P.asIdeal
        (Algebra.norm (𝓞 ℚ) b ^ ((Nat.card (𝓞 ℚ ⧸ P.asIdeal) - 1) / N))
      = Ideal.Quotient.mk P.asIdeal (((c ^ j' : ℕ) : 𝓞 ℚ)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 k), primeUnder (𝓞 ℚ) v = P →
      placeInvariant k v X = Multiplicative.ofAdd (zmodQModZ N ((j v : ℕ) : ZMod N)))
    (hlocP : placeInvariant ℚ P Z = Multiplicative.ofAdd (zmodQModZ N ((j' : ℕ) : ZMod N))) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        Set.mulIndicator {u | primeUnder (𝓞 ℚ) u = P} (fun u => placeInvariant k u X) v
      = placeInvariant ℚ P Z := by
  rw [finprod_placeInvariant_fibre_natCast X P j hloc, hlocP,
    natCast_finsum_eq_natCast_of_residue P (NeZero.ne N) hNP hord j hunram hres hres']

end FibreConductor

end InverseGalois.CFT
