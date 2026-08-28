/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Level

/-!
# Ramification forced by a square root

A number field containing a square root of a rational integer `n` cannot avoid ramification at the
primes that divide `n` exactly once, nor at `2` when `n` is congruent to `3` modulo `4`.  Both
statements come from a single observation about a prime `P` of the ring of integers above a
rational prime `p`: if two elements of the ring of integers lie in `P` and their product is a
rational integer divisible by `p` but not by `p ^ 2`, then `p` itself lies in `P ^ 2`, which is
exactly the failure of the ramification index to be one.

For the square root itself the two elements are the square root twice over, and the product is `n`.
For a square root of `n ≡ 3 mod 4` the two elements are the square root shifted by `1` in either
direction: they differ by `2`, so one of them lying above `2` forces the other to, and their
product is `n - 1`, which is twice an odd number.

Reading the two statements backwards bounds the integers that can become squares in a number field
with prescribed ramification: a squarefree integer that becomes a square in a field unramified at
`2` is congruent to `1` modulo `4`, and one that becomes a square in a field ramified only at `2`
divides `2`.

## Main results

* `InverseGalois.CFT.mem_ramifiedSet_of_sq_eq_intCast`: a prime dividing to the first order an
  integer with a square root in a number field ramifies in that field.
* `InverseGalois.CFT.two_mem_ramifiedSet_of_sq_eq_intCast`: `2` ramifies in a number field
  containing a square root of an integer congruent to `3` modulo `4`.
* `InverseGalois.CFT.emod_four_eq_one_of_sq_eq_intCast`: **a squarefree integer with a square root
  in a number field unramified at `2` is congruent to `1` modulo `4`.**
* `InverseGalois.CFT.dvd_two_of_sq_eq_intCast`: **a squarefree integer with a square root in a
  number field ramified only at `2` divides `2`.**

## Tags

ramification, square root, squarefree, quadratic field
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {K : Type*} [Field K] [NumberField K]

/-! ### The ramification criterion -/

/-- **A rational prime dividing a product to the first order ramifies.**  If two elements of the
ring of integers differ by a multiple of `p` and their product is a rational integer divisible by
`p` but not by `p ^ 2`, then any prime of the ring of integers above `p` contains both factors,
hence contains their product to order at least two, so its ramification index is not one. -/
theorem mem_ramifiedSet_of_mul_eq_intCast {p : ℕ} (hp : p.Prime) {a b : 𝓞 K} {c : ℤ}
    (hab : a * b = algebraMap ℤ (𝓞 K) c)
    (hsub : algebraMap ℤ (𝓞 K) (p : ℤ) ∣ a - b)
    (hdvd : (p : ℤ) ∣ c) (hndvd : ¬ ((p : ℤ) ^ 2 ∣ c)) : p ∈ ramifiedSet K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨P, hPprime, hPover⟩⟩ := Ideal.nonempty_primesOver (Ideal.span {(p : ℤ)}) (S := 𝓞 K)
  haveI := hPprime
  haveI := hPover
  set π : 𝓞 K := algebraMap ℤ (𝓞 K) (p : ℤ) with hπ
  -- for a rational integer, membership in `P` is divisibility by `p`
  have hmemP : ∀ z : ℤ, algebraMap ℤ (𝓞 K) z ∈ P ↔ (p : ℤ) ∣ z := by
    intro z
    constructor
    · intro h
      have hz : z ∈ Ideal.under ℤ P := Ideal.mem_comap.mpr h
      rw [← hPover.over, Ideal.mem_span_singleton] at hz
      exact hz
    · rintro ⟨w, rfl⟩
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_comap.mp
        (by rw [← Ideal.under_def, ← hPover.over]; exact Ideal.mem_span_singleton_self _))
  have hπP : π ∈ P := (hmemP _).mpr dvd_rfl
  obtain ⟨c', rfl⟩ := hdvd
  have hpc' : ¬ ((p : ℤ) ∣ c') := by
    rintro ⟨d, rfl⟩
    exact hndvd ⟨d, by ring⟩
  have hc'P : algebraMap ℤ (𝓞 K) c' ∉ P := fun h => hpc' ((hmemP c').mp h)
  -- both factors lie in `P`
  obtain ⟨w, hw⟩ := hsub
  have habP : a * b ∈ P := by
    rw [hab]
    exact (hmemP _).mpr ⟨c', rfl⟩
  have haP : a ∈ P := by
    rcases hPprime.mem_or_mem habP with h | h
    · exact h
    · have heq : a = b + π * w := by rw [← hw]; ring
      rw [heq]
      exact P.add_mem h (Ideal.mul_mem_right _ _ hπP)
  have hbP : b ∈ P := by
    have heq : b = a - π * w := by rw [← hw]; ring
    rw [heq]
    exact P.sub_mem haP (Ideal.mul_mem_right _ _ hπP)
  -- the prime is nonzero, hence prime as an element of the monoid of ideals
  have hπ0 : π ≠ 0 := by
    rw [hπ, Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
    exact_mod_cast hp.ne_zero
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hπP
    exact hπ0 hπP
  have hPmonoid : Prime P := Ideal.prime_of_isPrime hP0 hPprime
  -- the square of the prime contains `p`
  have hle2 : Ideal.span {π} ≤ P ^ 2 := by
    have hmul : P ^ 2 ∣ Ideal.span {π} * Ideal.span {algebraMap ℤ (𝓞 K) c'} := by
      rw [Ideal.span_singleton_mul_span_singleton, Ideal.dvd_iff_le, Ideal.span_le,
        Set.singleton_subset_iff, sq]
      have heq : π * algebraMap ℤ (𝓞 K) c' = a * b := by rw [hab, hπ, ← map_mul]
      rw [heq]
      exact Ideal.mul_mem_mul haP hbP
    have hnd : ¬ P ∣ Ideal.span {algebraMap ℤ (𝓞 K) c'} := by
      rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
      exact hc'P
    exact Ideal.dvd_iff_le.mp (hPmonoid.pow_dvd_of_dvd_mul_right 2 hnd hmul)
  have hle1 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≤ P := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hπP
  refine ⟨hp, P, ⟨hPprime, hPover⟩, ?_⟩
  rw [Ideal.ramificationIdx_ne_one_iff hle1, Ideal.map_span, Set.image_singleton]
  exact hle2

omit [NumberField K] in
/-- A square root of a rational integer is an algebraic integer. -/
theorem isIntegral_of_sq_eq_intCast {y : K} {n : ℤ} (hy : y ^ 2 = (n : K)) : IsIntegral ℤ y := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C n, Polynomial.monic_X_pow_sub_C n two_ne_zero, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, hy]
  simp

omit [NumberField K] in
/-- The image of a rational integer in the ring of integers has the expected value. -/
theorem algebraMap_algebraMap_int (n : ℤ) :
    algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) n) = (n : K) := by
  rw [← IsScalarTower.algebraMap_apply]
  simp

/-- **A prime dividing an integer to the first order ramifies in a field containing a square root
of that integer.** -/
theorem mem_ramifiedSet_of_sq_eq_intCast {y : K} {n : ℤ} (hy : y ^ 2 = (n : K)) {p : ℕ}
    (hp : p.Prime) (hdvd : (p : ℤ) ∣ n) (hndvd : ¬ ((p : ℤ) ^ 2 ∣ n)) : p ∈ ramifiedSet K := by
  have hint : IsIntegral ℤ y := isIntegral_of_sq_eq_intCast hy
  set Y : 𝓞 K := ⟨y, hint⟩ with hYdef
  have hYval : algebraMap (𝓞 K) K Y = y := rfl
  refine mem_ramifiedSet_of_mul_eq_intCast hp (a := Y) (b := Y) ?_ ⟨0, by ring⟩ hdvd hndvd
  apply NumberField.RingOfIntegers.coe_injective
  rw [map_mul, hYval, algebraMap_algebraMap_int, ← hy]
  ring

/-- **Two ramifies in a field containing a square root of an integer congruent to three modulo
four.**  The square root shifted by one in either direction gives two elements differing by `2`
whose product is `n - 1`, an integer that is twice an odd number. -/
theorem two_mem_ramifiedSet_of_sq_eq_intCast {y : K} {n : ℤ} (hy : y ^ 2 = (n : K))
    (hn : n % 4 = 3) : 2 ∈ ramifiedSet K := by
  have hint : IsIntegral ℤ y := isIntegral_of_sq_eq_intCast hy
  have hcast : algebraMap ℤ (𝓞 K) ((2 : ℕ) : ℤ) = 2 := by
    rw [show (((2 : ℕ) : ℤ)) = (2 : ℤ) from by norm_num, map_ofNat]
  have h4 : ((2 : ℕ) : ℤ) ^ 2 = 4 := by norm_num
  set Y : 𝓞 K := ⟨y, hint⟩ with hYdef
  have hYval : algebraMap (𝓞 K) K Y = y := rfl
  refine mem_ramifiedSet_of_mul_eq_intCast Nat.prime_two (a := Y - 1)
    (b := Y + 1) (c := n - 1) ?_ ⟨-1, ?_⟩ ?_ ?_
  · apply NumberField.RingOfIntegers.coe_injective
    rw [map_mul, map_sub, map_add, map_one, hYval, algebraMap_algebraMap_int,
      show ((y - 1) * (y + 1) : K) = y ^ 2 - 1 from by ring, hy]
    push_cast
    ring
  · rw [hcast]
    ring
  · push_cast
    omega
  · rw [h4]
    omega

/-! ### Squarefree integers that become squares -/

/-- **A squarefree integer with a square root in a number field unramified at two is congruent to
one modulo four.** -/
theorem emod_four_eq_one_of_sq_eq_intCast {y : K} {n : ℤ} (hsqf : Squarefree n)
    (hy : y ^ 2 = (n : K)) (h2 : 2 ∉ ramifiedSet K) : n % 4 = 1 := by
  have hnu : ¬ IsUnit (2 : ℤ) := by
    rw [Int.isUnit_iff]
    omega
  have h4 : ((2 : ℕ) : ℤ) ^ 2 = 4 := by norm_num
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · exact absurd (hsqf 2 (by rw [show (2 : ℤ) * 2 = 4 from by norm_num]; omega)) hnu
  · exact h
  · refine absurd ?_ h2
    refine mem_ramifiedSet_of_sq_eq_intCast hy Nat.prime_two (by push_cast; omega) ?_
    rw [h4]
    omega
  · exact absurd (two_mem_ramifiedSet_of_sq_eq_intCast hy h) h2

/-- **A squarefree integer with a square root in a number field ramified only at two divides
two.**  Every odd prime factor would ramify. -/
theorem dvd_two_of_sq_eq_intCast {y : K} {n : ℤ} (hsqf : Squarefree n) (hy : y ^ 2 = (n : K))
    (hram : ramifiedSet K ⊆ {2}) : n ∣ 2 := by
  classical
  have hsqfn : Squarefree n.natAbs := Int.squarefree_natAbs.mpr hsqf
  have hsub : n.natAbs.primeFactors ⊆ ({2} : Finset ℕ) := by
    intro p hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpdvd : (p : ℤ) ∣ n := by
      rw [← Int.natAbs_dvd_natAbs]
      simpa using Nat.dvd_of_mem_primeFactors hpmem
    have hpn2 : ¬ ((p : ℤ) ^ 2 ∣ n) := by
      intro hd
      refine absurd (hsqf (p : ℤ) ?_) ?_
      · rw [show ((p : ℤ)) * (p : ℤ) = (p : ℤ) ^ 2 from by ring]
        exact hd
      · rw [Int.isUnit_iff]
        have := hp.two_le
        omega
    have := hram (mem_ramifiedSet_of_sq_eq_intCast hy hp hpdvd hpn2)
    simpa using this
  have hprod : n.natAbs ∣ 2 := by
    calc n.natAbs = ∏ q ∈ n.natAbs.primeFactors, q :=
          (Nat.prod_primeFactors_of_squarefree hsqfn).symm
      _ ∣ ∏ q ∈ ({2} : Finset ℕ), q := Finset.prod_dvd_prod_of_subset _ _ _ hsub
      _ = 2 := by simp
  exact Int.natAbs_dvd.mp (by exact_mod_cast hprod)

/-! ### Integers that are squares of rational numbers -/

/-- An integer that is the square of a rational number is the square of an integer. -/
theorem exists_sq_eq_of_sq_eq_ratCast {n : ℤ} {r : ℚ} (h : (n : ℚ) = r ^ 2) :
    ∃ k : ℤ, n = k ^ 2 := by
  have hint : IsIntegral ℤ r := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C n, Polynomial.monic_X_pow_sub_C n two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, ← h]
    simp
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨k, ?_⟩
  have : ((n : ℚ)) = ((k : ℚ)) ^ 2 := by
    rw [h, ← hk]
    simp
  exact_mod_cast this

end InverseGalois.CFT
