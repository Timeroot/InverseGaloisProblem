/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.BaseCyclicClass
import InverseGalois.CFT.Brauer.SplitBase

/-!
# Reciprocity over a number field for a class whose bad primes are non-residues

Over the rationals a Brauer class of prime-power order is shown to satisfy reciprocity by splitting
it over the subfield of prescribed degree of the cyclotomic field of an auxiliary prime: the order
of the decomposition group of that subfield at a bad prime is read off from a power residue
condition, and a bad prime failing that condition has a decomposition group large enough to kill
the local invariant.  Over an arbitrary base the same subfield is composed with the base, and the
argument survives with one change.

The change is that the decomposition group of the compositum over the base is no longer the
decomposition group of the subfield over the rationals.  The two differ by the residue degree the
base itself contributes at the rational prime, which is at most the degree of the base.  So the
power residue condition is only reached after enlarging the exponent by the multiplicity of the
prime in that degree, which is what the logarithm in the hypothesis records: the auxiliary prime is
asked to be congruent to one modulo a correspondingly larger power.

## Main results

* `InverseGalois.CFT.totalInvariant_eq_one_of_forall_pow_ne_one_primePow_base`: **the invariants of
  a Brauer class of a number field, of prime-power order and trivial at the infinite places, add up
  to zero as soon as every rational prime below a place carrying a nontrivial invariant fails a
  power residue condition modulo an auxiliary prime.**

## Tags

Brauer group, local invariant, global reciprocity, cyclotomic field, power residue symbol,
auxiliary prime, decomposition group, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField InverseGalois.NumberTheory

open scoped Pointwise

/-! ### Reciprocity for a class of prime-power order -/

section Reciprocity

/-- **Reciprocity for a Brauer class of a number field of prime-power order all of whose bad primes
fail a power residue condition modulo an auxiliary prime.**  The compositum of the base with the
subfield of degree a power of the prime of the cyclotomic field of the auxiliary prime is a cyclic
extension of that degree satisfying reciprocity, and the order of its decomposition group at a
place is, up to the residue degree of the base, the order of the decomposition group of the
subfield, which a power residue condition names.  A bad prime therefore has a decomposition group
large enough to kill the local invariant, so the class is split by the compositum.  The excess of
the degree over the order of the class must absorb the multiplicity of the prime in the degree of
the base. -/
theorem totalInvariant_eq_one_of_forall_pow_ne_one_primePow_base (k : Type) [Field k]
    [NumberField k] {ℓ d e : ℕ} (hℓ : ℓ.Prime) (he : e ≠ 0)
    (hed : e + Nat.log ℓ (finrank ℚ k) ≤ d) {x : BrauerGroup.{0, 0} k}
    (harch : ∀ u : InfinitePlace k, infinitePlaceInvariant k u x = 1) (hx : x ^ ℓ ^ e = 1)
    {q : ℕ} (hq : q.Prime) (hqk : q ∉ ramifiedSet k) (hdvd : 2 * ℓ ^ d ∣ q - 1)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x ≠ 1 →
      ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 k) ∈ v.asIdeal →
        p ≠ q ∧ ((p : ℕ) : ZMod q)
          ^ ((q - 1) / ℓ ^ (d - e - Nat.log ℓ (finrank ℚ k) + 1)) ≠ 1) :
    totalInvariant k x = 1 := by
  set t := Nat.log ℓ (finrank ℚ k) with ht
  have hNdvd : ℓ ^ d ∣ q - 1 := dvd_trans ⟨2, mul_comm 2 (ℓ ^ d)⟩ hdvd
  have hsplitpow : ℓ ^ d = ℓ ^ (d - e - t + 1) * ℓ ^ (t + (e - 1)) := by
    rw [← pow_add]
    congr 1
    omega
  have harith : ℓ ^ (t + (e - 1)) * ((q - 1) / ℓ ^ d) = (q - 1) / ℓ ^ (d - e - t + 1) := by
    obtain ⟨c, hc⟩ := hNdvd
    rw [hc, Nat.mul_div_cancel_left _ (pow_pos hℓ.pos d), hsplitpow, mul_assoc,
      Nat.mul_div_cancel_left _ (pow_pos hℓ.pos (d - e - t + 1))]
  obtain ⟨g, hg, hgord⟩ := exists_nat_primitiveRoot_of_prime hq
  obtain ⟨E, _, _, _, _, hcycE, hcardE, hrec, hdec, -⟩ :=
    exists_subcyclotomicSplittingField_base k hq hqk (pow_ne_zero d hℓ.ne_zero) hdvd hg hgord
  haveI := hcycE
  refine hrec x (mem_relative_of_forall_not_dvd_primePow_base hℓ hx harch E hcardE ?_)
  intro w hinv hD
  obtain ⟨p, hp, -, hlies⟩ := exists_prime_primeUnder_eq_ratPlace w
  haveI := hlies
  have hpmem : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := natCast_mem_of_liesOver_span (q := p) w.asIdeal
  have hpmemk : ((p : ℕ) : 𝓞 k) ∈ (primeUnder (𝓞 k) w).asIdeal := by
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hpmem
  obtain ⟨hpq, hres⟩ := hbad (primeUnder (𝓞 k) w) hinv p hp hpmemk
  obtain ⟨A, n, hAN, hn0, hnle, hAdvd, hAm⟩ := hdec w p hp hpq hpmem
  obtain ⟨s, hsle, hDs⟩ := (Nat.dvd_prime_pow hℓ).mp hD
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow hℓ).mp hAN
  rw [hDs] at hAdvd
  have hnt : ¬ ℓ ^ (t + 1) ∣ n := by
    intro hcon
    have h1 : ℓ ^ (t + 1) ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hcon
    have h2 : finrank ℚ k < ℓ ^ (t + 1) := Nat.lt_pow_succ_log_self hℓ.one_lt _
    omega
  have hat : a ≤ t + s := le_add_of_pow_dvd_mul hℓ hn0 hnt hAdvd
  have hkey := hAm (ℓ ^ (t + (e - 1))) (pow_dvd_pow ℓ (by omega))
  rw [harith] at hkey
  exact hres hkey

end Reciprocity

end InverseGalois.CFT
