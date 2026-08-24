/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Clearing a denominator away from one place

An element of the fraction field of a Dedekind domain which is integral at a given place can be
multiplied into the domain by a scalar which is a unit at that place.  The point is that the
correcting factor does not disturb the place one cares about, so a fraction integral there becomes
an algebraic integer without losing the information that it is a unit.

The proof is the Chinese remainder theorem.  Write the element as a quotient with a common
denominator; the denominator is divisible by only finitely many primes, and at each of them one
knows how large a power of the prime is needed.  A single element of the domain can be prescribed
to be congruent to one at the given place and to lie in the required power of each of the finitely
many other primes, and that element is the required scalar.

## Main results

* `InverseGalois.CFT.exists_notMem_smul_mem`: **an element integral at a place becomes integral
  everywhere after multiplication by a scalar which is a unit at that place.**

## Tags

Dedekind domain, fraction field, denominator, place, Chinese remainder theorem
-/

namespace InverseGalois.CFT

open IsDedekindDomain

section Denominator

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

omit [IsDomain R] in
/-- For a nonzero element of a Dedekind domain, the valuation at a place is the exponential of the
negative of a natural number, namely the multiplicity of the place in the principal ideal. -/
private theorem exists_intValuation_eq_exp {d : R} (hd : d ≠ 0) (u : HeightOneSpectrum R) :
    ∃ n : ℕ, u.intValuation d = WithZero.exp (-(n : ℤ)) := by
  classical
  exact ⟨(Associates.mk u.asIdeal).count (Associates.mk (Ideal.span {d})).factors,
    u.intValuation_if_neg hd⟩

/-- **Clearing the denominator of a fraction without touching a given place**: if an element of the
fraction field is integral at a place, some element of the ring which is a unit at that place
multiplies it into the ring. -/
theorem exists_notMem_smul_mem {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) {a : K} (ha : v.valuation K a ≤ 1) :
    ∃ t : R, t ∉ v.asIdeal ∧ ∃ r : R, algebraMap R K t * a = algebraMap R K r := by
  classical
  obtain ⟨⟨c, d, hd⟩, hcd⟩ := IsLocalization.surj (nonZeroDivisors R) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  simp only at hcd
  choose e he using fun u => exists_intValuation_eq_exp hd0 u
  have he0 : ∀ u : HeightOneSpectrum R, ¬ u.asIdeal ∣ Ideal.span {d} → e u = 0 := by
    intro u hu
    have h1 : ¬ u.intValuation d < 1 := fun h => hu ((u.intValuation_lt_one_iff_dvd d).1 h)
    have h2 : u.intValuation d = 1 := le_antisymm (u.intValuation_le_one d) (not_lt.1 h1)
    have h3 := (he u).symm.trans h2
    rw [← WithZero.exp_zero, WithZero.exp_inj] at h3
    exact_mod_cast neg_eq_zero.1 h3
  have hEfin : {u : HeightOneSpectrum R | u.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hd0)
  set s : Finset (HeightOneSpectrum R) := insert v hEfin.toFinset with hs
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun u : HeightOneSpectrum R => u.asIdeal) (fun u => if u = v then 1 else e u)
    (fun u _ => Ideal.prime_of_isPrime u.ne_bot u.isPrime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun u : s => if (u : HeightOneSpectrum R) = v then 1 else 0)
  have hvs : v ∈ s := Finset.mem_insert_self _ _
  have htv : t - 1 ∈ v.asIdeal := by simpa using ht v hvs
  have htnotmem : t ∉ v.asIdeal := by
    intro h
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (by simpa using v.asIdeal.sub_mem h htv)
      isUnit_one)
  have key : ∀ u : HeightOneSpectrum R, u ≠ v → t ∈ u.asIdeal ^ e u := by
    intro u huv
    by_cases hu : u.asIdeal ∣ Ideal.span {d}
    · have hus : u ∈ s := Finset.mem_insert_of_mem (hEfin.mem_toFinset.2 hu)
      simpa [huv] using ht u hus
    · simp [he0 u hu, Ideal.one_eq_top]
  have hint : ∀ u : HeightOneSpectrum R, u.valuation K (algebraMap R K t * a) ≤ 1 := by
    intro u
    rw [map_mul]
    by_cases huv : u = v
    · subst huv
      calc u.valuation K (algebraMap R K t) * u.valuation K a
          ≤ 1 * 1 := mul_le_mul' (u.valuation_le_one t) ha
        _ = 1 := one_mul 1
    · have h1 : u.valuation K (algebraMap R K t) ≤ u.valuation K (algebraMap R K d) := by
        rw [u.valuation_of_algebraMap, u.valuation_of_algebraMap, he u]
        exact (u.intValuation_le_pow_iff_mem t (e u)).2 (key u huv)
      have h2 : u.valuation K (algebraMap R K d) * u.valuation K a ≤ 1 := by
        rw [mul_comm, ← map_mul, hcd, u.valuation_of_algebraMap]
        exact u.intValuation_le_one c
      exact le_trans (mul_le_mul_left h1 _) h2
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ hint
  exact ⟨t, htnotmem, r, hr.symm⟩

end Denominator

end InverseGalois.CFT
