/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceConductor
import InverseGalois.CFT.Brauer.RatCount
import InverseGalois.CFT.Cyclotomic.SubfieldNorm
import InverseGalois.CFT.RatUnits

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

The two remaining coefficients are the conductor itself and `-1`, and for those the cyclic algebra
is already trivial: the conductor is the norm of one less than a primitive root of unity, and `-1`
is the norm of `-1` from a field of odd degree.  Since `-1` and the rational primes generate the
units of the rationals, the total invariant then vanishes for every coefficient.

## Main results

* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom_subcyclotomic_eq_one`: **the sum of all the
  local invariants of a cyclic algebra over the rationals split by a totally real subfield of the
  cyclotomic field of an odd prime conductor, with a rational prime away from the conductor as
  coefficient, vanishes.**
* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom_subcyclotomic`: **the same for an arbitrary
  rational coefficient**, when the splitting field has odd degree.

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
    {N : ℕ} [NeZero N] (hNodd : Odd N) (hcard : Nat.card Gal(F/ℚ) = N)
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
  have hinvq := placeInvariant_cyclicBrauerHom_conductor q L F hq.out hodd Wq hNodd hcard hinert hg
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

/-! ### Every coefficient -/

/-- **The sum of all the local invariants of a cyclic algebra over the rationals split by a totally
real subfield of odd degree of the cyclotomic field of an odd prime conductor vanishes**, for
every rational coefficient.  The units of the rationals are generated by `-1` and the rational
primes; a prime away from the conductor is the case already settled by the two-place cancellation,
while the conductor and `-1` are norms from the splitting field, so their algebras are trivial. -/
theorem totalInvariant_cyclicBrauerHom_subcyclotomic [hq : Fact q.Prime] (hodd : Odd q) {N : ℕ}
    [NeZero N] (hNodd : Odd N) (hcard : Nat.card Gal(F/ℚ) = N)
    (hinertia : ∀ (Q : Ideal (𝓞 F)) (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.span {(q : ℤ)})),
      Ideal.inertia Gal(F/ℚ) Q = ⊤)
    {g : ℕ} (hg : Nat.Coprime g q) (hgord : ∀ k : ℕ, q ∣ g ^ k - 1 → (q - 1) ∣ k)
    (hgen : ∀ x : Gal(L/ℚ), x ∈ Subgroup.zpowers (cyclotomicPowerAut q L hg)) (a : ℚˣ) :
    totalInvariant ℚ (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := F) hgen) a)
      = 1 := by
  have hq2 : q ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hodd
    omega
  have hfin : Module.finrank ℚ F = N := by
    rw [← IsGalois.card_aut_eq_finrank ℚ F]
    exact hcard
  have hker : ∀ u : ℚˣ, (∃ b : Fˣ, Algebra.norm ℚ (b : F) = (u : ℚ)) →
      totalInvariant ℚ (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := F) hgen) u)
        = 1 := by
    intro u hu
    have hmem := (mem_ker_cyclicBrauerHom_iff
      (forall_mem_zpowers_restrictNormal (L := F) hgen) u).mpr hu
    rw [MonoidHom.mem_ker] at hmem
    rw [hmem, map_one]
  have hneg : ((totalInvariant ℚ).comp
      (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := F) hgen))) (-1) = 1 := by
    rw [MonoidHom.comp_apply]
    refine hker _ ?_
    obtain ⟨b, hb⟩ := exists_units_norm_eq_neg_one F (by rw [hfin]; exact hNodd)
    exact ⟨b, by rw [hb, Units.val_neg, Units.val_one]⟩
  have hprime : ∀ (p : ℕ) (u : ℚˣ), p.Prime → (u : ℚ) = (p : ℚ) →
      ((totalInvariant ℚ).comp
        (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := F) hgen))) u = 1 := by
    intro p u hp hu
    rw [MonoidHom.comp_apply]
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hpq : p = q
    · refine hker _ ?_
      obtain ⟨b, hb⟩ := exists_units_norm_eq_conductor q L F hq2
      exact ⟨b, by rw [hb, hu, hpq]⟩
    · exact totalInvariant_cyclicBrauerHom_subcyclotomic_eq_one q L F hodd hNodd hcard hinertia hg
        hgord hgen hpq hu
  exact eq_one_of_neg_one_of_prime ((totalInvariant ℚ).comp
    (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := F) hgen))) hneg hprime a

end Reciprocity

end InverseGalois.CFT
