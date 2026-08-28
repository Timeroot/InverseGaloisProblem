/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Disjoint
import InverseGalois.CFT.SqrtCompositum

/-!
# A square root acquired by a compositum with a field ramified elsewhere

A square root lying in a compositum of two Galois extensions meeting in the rationals splits as a
product of a square root from each factor, and the squarefree part of each half is divisible only
by primes ramifying in that half.  When the two halves ramify at disjoint sets of primes, the second
of which avoids two, and the radicand itself is divisible only by primes ramifying in the first
half, the squarefree part of the second half has to be one: a prime dividing it would divide the
product of the radicand with the two squarefree parts exactly once, and that product is a square.

So enlarging a field by an extension ramified somewhere else acquires no new square root of an
integer supported on the primes already ramifying.

## Main results

* `InverseGalois.CFT.mem_ramifiedSet_of_squarefree_of_sq_eq_intCast`: a prime dividing a squarefree
  integer with a square root in a number field ramifies there.
* `InverseGalois.CFT.mem_of_sq_eq_intCast_of_ramifiedSet_disjoint`: **a square root of an integer
  supported on the primes ramifying in the first factor, lying in a compositum with a factor
  ramifying at disjoint primes, lies in the first factor.**

## Tags

square root, compositum, ramification, squarefree, disjoint
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Primes of a squarefree radicand -/

/-- **A prime dividing a squarefree integer with a square root in a number field ramifies
there.**  A squarefree integer is divisible by no square of a prime, so the prime divides it
exactly once. -/
theorem mem_ramifiedSet_of_squarefree_of_sq_eq_intCast {K : Type*} [Field K] [NumberField K]
    {y : K} {n : ℤ} (hsqf : Squarefree n) (hy : y ^ 2 = (n : K)) {p : ℕ} (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ n) : p ∈ ramifiedSet K := by
  refine mem_ramifiedSet_of_sq_eq_intCast hy hp hdvd fun hd => ?_
  refine absurd (hsqf (p : ℤ) ?_) ?_
  · rw [show ((p : ℤ)) * (p : ℤ) = (p : ℤ) ^ 2 from by ring]
    exact hd
  · rw [Int.isUnit_iff]
    have := hp.two_le
    omega

/-! ### The compositum -/

set_option maxHeartbeats 1000000 in
/-- **A square root of an integer supported on the primes ramifying in the first factor, lying in a
compositum with a factor ramifying at disjoint primes, lies in the first factor.**  The squarefree
part of the second half is congruent to one modulo four, that factor not ramifying at two, and the
product of the integer with the two squarefree parts is a perfect square; a prime of the second
squarefree part divides that product exactly once, which is impossible, so the second squarefree
part is one and the second half of the square root is rational. -/
theorem mem_of_sq_eq_intCast_of_ramifiedSet_disjoint {L : Type*} [Field L] [CharZero L]
    (A B : IntermediateField ℚ L) [NumberField ↥A] [NumberField ↥B]
    [FiniteDimensional ℚ ↥(A ⊔ B)] [IsGalois ℚ ↥(A ⊔ B)] [IsGalois ℚ ↥A] [IsGalois ℚ ↥B]
    (hinf : A ⊓ B = ⊥) (hB2 : 2 ∉ ramifiedSet ↥B)
    (hdisj : Disjoint (ramifiedSet ↥A) (ramifiedSet ↥B)) {m : ℤ} (hm0 : m ≠ 0)
    (hmA : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → p ∈ ramifiedSet ↥A) {x : L} (hx : x ∈ A ⊔ B)
    (hxm : x ^ 2 = (m : L)) : x ∈ A := by
  classical
  have hinj : Function.Injective (algebraMap ℚ L) := (algebraMap ℚ L).injective
  have hmL : ((m : L)) ≠ 0 := Int.cast_ne_zero.mpr hm0
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hxm
    exact hmL hxm.symm
  have hb : x ^ 2 = algebraMap ℚ L ((m : ℚ)) := by rw [hxm, map_intCast]
  obtain ⟨y, hyA, z, hzB, hxyz, ⟨c, hc⟩, ⟨d, hd⟩⟩ :=
    exists_mul_eq_of_sq_mem_sup A B hinf hx hb
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hxyz, zero_mul])
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hxyz, mul_zero])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, pow_eq_zero_iff two_ne_zero] at hc
    exact hy0 hc
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero, pow_eq_zero_iff two_ne_zero] at hd
    exact hz0 hd
  have hcd : ((m : ℚ)) = c * d := by
    refine hinj ?_
    rw [← hb, hxyz, mul_pow, hc, hd, map_mul]
  -- the squarefree parts of the two factors
  obtain ⟨sc, tc, hsc0, hscsf, htc0, hceq⟩ := exists_squarefree_intCast_mul_sq hc0
  obtain ⟨sd, td, hsd0, hsdsf, htd0, hdeq⟩ := exists_squarefree_intCast_mul_sq hd0
  -- the square root of the squarefree part of each factor lies in that factor
  have hwA : y / algebraMap ℚ L tc ∈ A := div_mem hyA (A.algebraMap_mem tc)
  have hw2 : (y / algebraMap ℚ L tc) ^ 2 = ((sc : ℤ) : L) := by
    rw [div_pow, hc, ← map_pow, ← map_div₀,
      show c / tc ^ 2 = ((sc : ℚ)) from by rw [hceq]; field_simp, map_intCast]
  have hvB : z / algebraMap ℚ L td ∈ B := div_mem hzB (B.algebraMap_mem td)
  have hv2 : (z / algebraMap ℚ L td) ^ 2 = ((sd : ℤ) : L) := by
    rw [div_pow, hd, ← map_pow, ← map_div₀,
      show d / td ^ 2 = ((sd : ℚ)) from by rw [hdeq]; field_simp, map_intCast]
  have hsdmod : sd % 4 = 1 :=
    emod_four_eq_one_of_sq_eq_intCast (K := ↥B) hsdsf (sq_eq_intCast_coe B hvB hv2) hB2
  have hscram : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ sc → p ∈ ramifiedSet ↥A := fun p hp hpd =>
    mem_ramifiedSet_of_squarefree_of_sq_eq_intCast (K := ↥A) hscsf
      (sq_eq_intCast_coe A hwA hw2) hp hpd
  have hsdram : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ sd → p ∈ ramifiedSet ↥B := fun p hp hpd =>
    mem_ramifiedSet_of_squarefree_of_sq_eq_intCast (K := ↥B) hsdsf
      (sq_eq_intCast_coe B hvB hv2) hp hpd
  -- the integer times the two squarefree parts is a perfect square
  have hmcd : ((m : ℚ)) = (sc : ℚ) * tc ^ 2 * ((sd : ℚ) * td ^ 2) := by rw [hcd, ← hceq, ← hdeq]
  have hmr : ((m * sc * sd : ℤ) : ℚ) = ((sc : ℚ) * (sd : ℚ) * tc * td) ^ 2 := by
    push_cast
    linear_combination ((sc : ℚ) * (sd : ℚ)) * hmcd
  obtain ⟨k, hk⟩ := exists_sq_eq_of_sq_eq_ratCast hmr
  have hkk : m * sc * sd = k * k := by rw [hk]; ring
  -- the squarefree part of the second factor has no prime divisor
  have hsdnat : sd.natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpZ : (p : ℤ) ∣ sd := Int.dvd_natAbs.mp (by exact_mod_cast hpdvd)
    have hpB : p ∈ ramifiedSet ↥B := hsdram p hp hpZ
    have hprime : Prime ((p : ℤ)) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
    have hpm : ¬ ((p : ℤ) ∣ m) := fun h =>
      (Set.disjoint_left.mp hdisj (hmA p hp h)) hpB
    have hpsc : ¬ ((p : ℤ) ∣ sc) := fun h =>
      (Set.disjoint_left.mp hdisj (hscram p hp h)) hpB
    have hpmsc : ¬ ((p : ℤ) ∣ m * sc) := fun h => (hprime.dvd_mul.mp h).elim hpm hpsc
    have hpk : (p : ℤ) ∣ k := by
      refine (hprime.dvd_mul.mp ?_).elim id id
      rw [← hkk]
      exact Dvd.dvd.mul_left hpZ _
    have hsq : ((p : ℤ)) ^ 2 ∣ m * sc * sd := by
      rw [hkk, sq]
      exact mul_dvd_mul hpk hpk
    have hpsd : ((p : ℤ)) ^ 2 ∣ sd := hprime.pow_dvd_of_dvd_mul_left 2 hpmsc hsq
    refine absurd (hsdsf (p : ℤ) ?_) ?_
    · rw [show ((p : ℤ)) * (p : ℤ) = (p : ℤ) ^ 2 from by ring]
      exact hpsd
    · rw [Int.isUnit_iff]
      have := hp.two_le
      omega
  have hsd1 : sd = 1 := by
    rcases Int.natAbs_eq sd with h | h <;> rw [hsdnat] at h <;> omega
  -- so the second factor is rational
  have hzA : z ∈ A := by
    have hd' : d = td ^ 2 := by rw [hdeq, hsd1]; norm_num
    have hz2 : z ^ 2 = (algebraMap ℚ L td) ^ 2 := by rw [hd, hd', map_pow]
    have hfac : (z - algebraMap ℚ L td) * (z + algebraMap ℚ L td) = 0 := by linear_combination hz2
    rcases mul_eq_zero.mp hfac with h | h
    · rw [sub_eq_zero.mp h]
      exact A.algebraMap_mem td
    · rw [eq_neg_of_add_eq_zero_left h]
      exact neg_mem (A.algebraMap_mem td)
  rw [hxyz]
  exact mul_mem hyA hzA

end InverseGalois.CFT
