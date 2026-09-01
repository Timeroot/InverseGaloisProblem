/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceConductor
import InverseGalois.CFT.Brauer.RatCount

/-!
# Reciprocity for a cyclic algebra split by a subfield of a cyclotomic field

A cyclic algebra over the rationals whose splitting field is a totally real subfield of the
cyclotomic field of an odd prime conductor, and whose coefficient is a rational prime away from
that conductor, has only two nontrivial local invariants: the one at the coefficient and the one at
the conductor.  Both are now known, and they are opposite.

At the place of the coefficient the extension is unramified, and the invariant is the exponent
expressing the automorphism raising the roots of unity to the power of the coefficient as a power
of the chosen generator, with a minus sign coming from the coefficient being a uniformiser there.
At the place of the conductor the extension is totally ramified, and the power residue symbol reads
the discrete logarithm of the coefficient to the base of the primitive root naming the generator —
which is the very same exponent, with a plus sign.  The two cancel.

## Main results

* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom_subcyclotomic_eq_one`: **the sum of all the
  local invariants of a cyclic algebra over the rationals split by a totally real subfield of the
  cyclotomic field of an odd prime conductor, with a rational prime away from the conductor as
  coefficient, vanishes.**

## Tags

Brauer group, local invariant, cyclic algebra, cyclotomic field, reciprocity, power residue symbol,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### The two places cancel -/

section Reciprocity

variable (q : ℕ) [NeZero q] (L F : Type) [Field L] [NumberField L]
  [IsCyclotomicExtension {q} ℚ L] [IsGalois ℚ L] [Field F] [NumberField F] [Algebra F L]
  [IsScalarTower ℚ F L] [IsGalois ℚ F] [IsTotallyReal F]

/-- **The sum of all the local invariants of a cyclic algebra over the rationals split by a totally
real subfield of the cyclotomic field of an odd prime conductor, with a rational prime away from
the conductor as coefficient, vanishes.**  Only two places contribute: at the coefficient the
invariant is minus the exponent expressing the automorphism raising the roots of unity to the power
of the coefficient as a power of the generator, and at the conductor the power residue symbol reads
that same exponent with the opposite sign. -/
theorem totalInvariant_cyclicBrauerHom_subcyclotomic_eq_one [hq : Fact q.Prime] (hodd : Odd q)
    {N : ℕ} [NeZero N] (hN : N.Prime) (hcard : Nat.card Gal(F/ℚ) = N)
    (hinertia : ∀ (Q : Ideal (𝓞 F)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
      Ideal.inertia Gal(F/ℚ) Q = ⊤)
    {g : ℕ} (hg : Nat.Coprime g q) (hgord : ∀ k : ℕ, q ∣ g ^ k - 1 → (q - 1) ∣ k)
    (hgen : ∀ x : Gal(L/ℚ), x ∈ Subgroup.zpowers (cyclotomicPowerAut q L hg)) {p : ℕ}
    [hp : Fact p.Prime] (hpq : p ≠ q) {a : ℚˣ} (hap : (a : ℚ) = ((p : ℕ) : ℚ)) :
    totalInvariant ℚ (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := F) hgen) a)
      = 1 := by
  have hpqc : Nat.Coprime p q := (Nat.coprime_primes hp.out hq.out).mpr hpq
  obtain ⟨c, hc⟩ := exists_pow_eq_cyclotomicPowerAut q L hg hgen hpqc
  obtain ⟨Wq, hWq⟩ := exists_primeUnder_eq (𝓞 ℚ) (𝓞 L) (ratPlace q hq.out)
  obtain ⟨Wp, hWp⟩ := exists_primeUnder_eq (𝓞 ℚ) (𝓞 L) (ratPlace p hp.out)
  haveI := liesOver_span_of_primeUnder_eq_ratPlace hq.out Wq hWq
  haveI := liesOver_span_of_primeUnder_eq_ratPlace hp.out Wp hWp
  have hmemF : ((q : ℕ) : 𝓞 F) ∈ (primeUnder (𝓞 F) Wq).asIdeal := by
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact natCast_mem_of_liesOver_span (q := q) Wq.asIdeal
  haveI := liesOver_span_of_natCast_mem hq.out (primeUnder (𝓞 F) Wq) hmemF
  have hinert : Ideal.inertia Gal(F/ℚ) (primeUnder (𝓞 F) Wq).asIdeal = ⊤ :=
    hinertia _ (primeUnder (𝓞 F) Wq).isPrime inferInstance
  have hinvq := placeInvariant_cyclicBrauerHom_conductor q L F hq.out hodd Wq hN hcard hinert hg
    hgord hgen hpqc hc hap
  rw [primeUnder_eq_ratPlace hq.out (primeUnder (𝓞 F) Wq)] at hinvq
  have hNq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → ℓ = q := fun ℓ hℓ hd =>
    (Nat.prime_dvd_prime_iff_eq hℓ hq.out).mp hd
  rw [totalInvariant_cyclicBrauerHom_rat_eq_mul (forall_mem_zpowers_restrictNormal (L := F) hgen)
      q L hp.out hq.out hpq hNq hap,
    placeInvariant_cyclicBrauerHom_subcyclotomic_ratPlace q L F hgen Wp hpqc hc hap, hinvq, hcard,
    intQModZ_eq_zmodQModZ, ← ofAdd_add, ← map_add]
  have hzero : ((-(c : ℤ) : ℤ) : ZMod N) + (c : ZMod N) = 0 := by
    push_cast
    ring
  rw [hzero, map_zero, ofAdd_zero]

end Reciprocity

end InverseGalois.CFT
