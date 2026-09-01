/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclotomicGenerator
import InverseGalois.CFT.Brauer.PlaceSubcyclotomic
import InverseGalois.CFT.Brauer.RelativeTorsion
import InverseGalois.CFT.Brauer.SubcyclotomicSplit

/-!
# Prescribing the invariant of a Brauer class at a single prime

Reciprocity for a class of odd prime order is proved by moving its local invariants around until
only one of them is left, and moving them needs a supply of correcting classes: given a rational
prime and a prescribed value of that order, a class whose total invariant vanishes, whose invariant
at the prime is the prescribed value, and whose invariants are trivial everywhere else save at one
auxiliary place.  The cyclic algebra with the prime as coefficient, split by the subfield of that
degree of the cyclotomic field of the auxiliary prime, is such a class.

Its invariant at the prime is read off the Frobenius, which is the power of the chosen generator
naming the prime; that exponent is prime to the degree exactly when the prime is a power
non-residue modulo the auxiliary prime.  The invariant then generates the whole group of values of
that order, so every prescribed value is one of its powers, and raising the class to the matching
power leaves the vanishing of the other invariants untouched.

## Main results

* `InverseGalois.CFT.exists_pow_ofAdd_intQModZ_eq`: the class of an integer prime to a prime
  generates the elements of the rationals modulo the integers killed by that prime.
* `InverseGalois.CFT.not_dvd_of_natCast_pow_ne_one`: the exponent expressing a power non-residue as
  a power of a primitive root is prime to the exponent of the residue condition.
* `InverseGalois.CFT.exists_placeInvariant_eq_of_pow_ne_one`: **a Brauer class of the rationals
  with trivial total invariant, a prescribed invariant of odd prime order at a given prime, and
  trivial invariants away from that prime and an auxiliary one.**

## Tags

Brauer group, local invariant, reciprocity, cyclotomic field, power residue symbol, auxiliary
prime, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField InverseGalois.NumberTheory

/-! ### Generating the torsion of the rationals modulo the integers -/

section Torsion

/-- **The class of an integer invertible modulo an exponent generates the elements of the rationals
modulo the integers killed by that exponent.**  Such an element is the class of a residue, and the
integer is invertible among the residues, so the residue is a multiple of it. -/
theorem exists_pow_ofAdd_intQModZ_eq {N : ℕ} [NeZero N] {c : ℤ} (hc : IsUnit ((c : ZMod N)))
    {t : Multiplicative QModZ} (ht : t ^ N = 1) :
    ∃ e : ℕ, (Multiplicative.ofAdd (intQModZ N c)) ^ e = t := by
  have htor : Multiplicative.toAdd t ∈ nsmulTorsionQModZ N :=
    (pow_eq_one_iff_nsmul_toAdd t N).mp ht
  obtain ⟨k, hk⟩ := (mem_nsmulTorsionQModZ_iff_exists N).mp htor
  have hval : (((k * (c : ZMod N)⁻¹).val : ℕ) : ZMod N) = k * (c : ZMod N)⁻¹ := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hkey : ((((((k * (c : ZMod N)⁻¹).val : ℕ) : ℤ) * c : ℤ)) : ZMod N) = k := by
    push_cast
    rw [hval, mul_assoc, ZMod.inv_mul_of_unit _ hc, mul_one]
  refine ⟨(k * (c : ZMod N)⁻¹).val, ?_⟩
  rw [← ofAdd_nsmul, ← map_nsmul, nsmul_eq_mul, intQModZ_eq_zmodQModZ, hkey, hk]
  rfl

/-- The class of an integer prime to a prime exponent is invertible among the residues. -/
theorem isUnit_intCast_zmod_of_prime {N : ℕ} (hN : N.Prime) {c : ℤ} (hc : ¬ (N : ℤ) ∣ c) :
    IsUnit ((c : ZMod N)) := by
  haveI : Fact N.Prime := ⟨hN⟩
  exact (isUnit_iff_ne_zero).mpr fun h => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd c N).mp h)

end Torsion

/-! ### The discrete logarithm of a non-residue -/

section DiscreteLog

/-- **The exponent expressing a power non-residue as a power of a primitive root is prime to the
exponent of the residue condition.**  Were it a multiple, the non-residue would be a power of the
primitive root raised to the order of the group of units, hence one. -/
theorem not_dvd_of_natCast_pow_ne_one {q : ℕ} (hq : q.Prime) {g : ℕ} (hg : Nat.Coprime g q)
    {N : ℕ} (hNdvd : N ∣ q - 1) {p c : ℕ} (hpg : ((p : ℕ) : ZMod q) = ((g : ℕ) : ZMod q) ^ c)
    (hres : ((p : ℕ) : ZMod q) ^ ((q - 1) / N) ≠ 1) : ¬ N ∣ c := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hg0 : ((g : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    exact hq.ne_one (hg.symm.eq_one_of_dvd ((ZMod.natCast_eq_zero_iff g q).mp hz))
  rintro ⟨c', rfl⟩
  refine hres ?_
  have harith : N * c' * ((q - 1) / N) = (q - 1) * c' := by
    rw [mul_right_comm, Nat.mul_div_cancel' hNdvd]
  rw [hpg, ← pow_mul, harith, pow_mul, ZMod.pow_card_sub_one_eq_one hg0, one_pow]

end DiscreteLog

/-! ### The correcting class -/

section Corrector

/-- **A Brauer class of the rationals with trivial total invariant, a prescribed invariant of odd
prime order at a given prime, and trivial invariants away from that prime and an auxiliary one.**
The class is a power of the cyclic algebra with the given prime as coefficient, split by the
subfield of that degree of the cyclotomic field of the auxiliary prime; the exponent of the
Frobenius at the given prime is prime to the degree because the prime is a power non-residue, so
the invariant there runs over all the values of that order. -/
theorem exists_placeInvariant_eq_of_pow_ne_one {N : ℕ} (hN : N.Prime) (hNodd : Odd N) {q : ℕ}
    (hq : q.Prime) (hqdvd : 2 * N ∣ q - 1) {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    (hres : ((p : ℕ) : ZMod q) ^ ((q - 1) / N) ≠ 1) {t : Multiplicative QModZ} (ht : t ^ N = 1) :
    ∃ y : BrauerGroup.{0, 0} ℚ, y ^ N = 1 ∧ totalInvariant ℚ y = 1 ∧
      placeInvariant ℚ (ratPlace p hp) y = t ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ ratPlace p hp → v ≠ ratPlace q hq →
        placeInvariant ℚ v y = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with rfl | h
    · have h2 := Nat.le_of_dvd (by norm_num) hqdvd
      have h3 := hN.two_le
      omega
    · exact h
  have hNdvd : N ∣ q - 1 := dvd_trans ⟨2, mul_comm 2 N⟩ hqdvd
  haveI : IsGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isGalois {q} ℚ (CyclotomicField q ℚ)
  obtain ⟨F, hrank, hgal, hcyc, hreal, -, hinertia⟩ :=
    exists_intermediateField_subcyclotomic q hN.ne_zero hqdvd (CyclotomicField q ℚ)
  haveI := hgal
  haveI := hcyc
  haveI := hreal
  have hcard : Nat.card Gal(↥F/ℚ) = N := by
    rw [IsGalois.card_aut_eq_finrank ℚ ↥F, hrank]
  obtain ⟨g, hg, hgord⟩ := exists_nat_primitiveRoot_of_prime hq
  have hgen := forall_mem_zpowers_cyclotomicPowerAut q (CyclotomicField q ℚ) hq hg hgord
  have hσ₀ := forall_mem_zpowers_restrictNormal (L := ↥F) hgen
  have hpq' : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  obtain ⟨c, hc⟩ := exists_pow_eq_cyclotomicPowerAut q (CyclotomicField q ℚ) hg hgen hpq'
  obtain ⟨a, hap⟩ : ∃ a : ℚˣ, (a : ℚ) = ((p : ℕ) : ℚ) :=
    ⟨Units.mk0 _ (Nat.cast_ne_zero.mpr hp.ne_zero), rfl⟩
  -- The invariant at the given prime, read off the Frobenius.
  obtain ⟨W, hW⟩ := exists_primeUnder_eq (𝓞 ℚ) (𝓞 (CyclotomicField q ℚ)) (ratPlace p hp)
  haveI := liesOver_span_of_primeUnder_eq_ratPlace hp W hW
  have hinvp : placeInvariant ℚ (ratPlace p hp) (cyclicBrauerHom hσ₀ a)
      = Multiplicative.ofAdd (intQModZ N (-(c : ℤ))) := by
    have h := placeInvariant_cyclicBrauerHom_subcyclotomic_ratPlace q (CyclotomicField q ℚ) ↥F
      hgen W hpq' hc hap
    rwa [hcard] at h
  -- The invariants away from the given prime and the conductor.
  have hvan : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ ratPlace p hp → v ≠ ratPlace q hq →
      placeInvariant ℚ v (cyclicBrauerHom hσ₀ a) = 1 := by
    intro v hvp hvq
    refine placeInvariant_cyclicBrauerHom_rat_eq_one_of_notMem hσ₀ q (CyclotomicField q ℚ) v
      (fun ℓ hℓ hdvd hmem => hvq ?_) ?_
    · refine heightOneSpectrum_rat_eq_of_natCast_mem hq ?_ (natCast_mem_ratPlace q hq)
      rwa [← (Nat.prime_dvd_prime_iff_eq hℓ hq).mp hdvd]
    · rw [hap, valuation_natCast_eq_one_iff]
      intro hmem
      exact hvp (heightOneSpectrum_rat_eq_of_natCast_mem hp hmem (natCast_mem_ratPlace p hp))
  -- The total invariant and the order.
  have htot : totalInvariant ℚ (cyclicBrauerHom hσ₀ a) = 1 :=
    totalInvariant_cyclicBrauerHom_subcyclotomic q (CyclotomicField q ℚ) ↥F hqodd hNodd hcard
      hinertia hg hgord hgen a
  have hord : (cyclicBrauerHom hσ₀ a) ^ N = 1 := by
    have h := pow_finrank_eq_one_of_mem_relative (L := ↥F) (cyclicBrauerHom hσ₀ a)
      (cyclicBrauerHom_mem_relative hσ₀ a)
    rwa [hrank] at h
  -- The exponent to raise it to.
  have hpg : ((p : ℕ) : ZMod q) = ((g : ℕ) : ZMod q) ^ c :=
    natCast_zmod_eq_pow_of_cyclotomicPowerAut_eq_pow q (CyclotomicField q ℚ) hg hpq' hc
  have hNc : ¬ (N : ℤ) ∣ (-(c : ℤ)) := by
    rw [dvd_neg, Int.natCast_dvd_natCast]
    exact not_dvd_of_natCast_pow_ne_one hq hg hNdvd hpg hres
  obtain ⟨e, he⟩ := exists_pow_ofAdd_intQModZ_eq (isUnit_intCast_zmod_of_prime hN hNc) ht
  refine ⟨(cyclicBrauerHom hσ₀ a) ^ e, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hord, one_pow]
  · rw [map_pow, htot, one_pow]
  · rw [map_pow, hinvp, he]
  · intro v hvp hvq
    rw [map_pow, hvan v hvp hvq, one_pow]

end Corrector

end InverseGalois.CFT
