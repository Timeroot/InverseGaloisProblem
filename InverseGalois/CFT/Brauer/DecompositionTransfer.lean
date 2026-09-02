/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.InertiaDegRat
import InverseGalois.CFT.InertiaSubgroup
import InverseGalois.CFT.SplitCompositum
import InverseGalois.CFT.Units.FrobeniusPlace

/-!
# Comparing decomposition groups over the rationals and over a base field

A compositum of a number field with a Galois extension of the rationals has two Galois groups
above a place: the one of the compositum over the base and the one of the small extension over the
rationals.  They are abstractly isomorphic, but their decomposition groups at a place of the
compositum are not, because the base field may itself contribute residue degree at the rational
prime below.  This module measures the discrepancy.

The tool is the multiplicativity of the residue degree.  The absolute norm of a prime is the
rational prime below it raised to the residue degree over the integers, and it is also the
absolute norm of the prime below raised to the relative residue degree; comparing the two
expressions of the same power of a prime splits the residue degree over the integers as the
residue degree of the intermediate prime times the relative residue degree.  Applying this to both
intermediate fields and using that the relative residue degree over the base divides the order of
the decomposition group over the base gives the comparison.

At a prime unramified in a Galois extension of the rationals the order of the decomposition group
is exactly the residue degree, the inertia subgroup being trivial there.  So the discrepancy is
bounded by the residue degree of the base, which never exceeds its degree; a divisibility of a
prime power by such a product then bounds the exponent by the sum of the exponent of the base
contribution and the exponent of the decomposition group.

## Main results

* `InverseGalois.CFT.card_stabilizer_eq_inertiaDeg_of_notMem_ramifiedSet`: **at an unramified
  prime the order of the decomposition group is the residue degree.**
* `InverseGalois.CFT.inertiaDeg_span_mul_of_under`: **the residue degree over the integers is
  multiplicative in a tower.**
* `InverseGalois.CFT.inertiaDeg_span_pos_le_finrank`: the residue degree over the rational prime a
  place contains is positive and at most the degree of the field.
* `InverseGalois.CFT.inertiaDeg_span_dvd_mul_card_stabilizer`: **the residue degree of an
  intermediate field divides the residue degree of the base times the order of the decomposition
  group over the base.**
* `InverseGalois.CFT.le_add_of_pow_dvd_mul`: a power of a prime dividing a product bounds its
  exponent by the exponents of the factors.

## Tags

number field, decomposition group, residue degree, inertia degree, absolute norm, compositum
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField InverseGalois.NumberTheory

open scoped Pointwise

/-! ### The decomposition group at an unramified prime -/

section Unramified

/-- **At a prime of a Galois number field unramified over the rationals the order of the
decomposition group is the residue degree.**  The order of the decomposition group is the
ramification index times the residue degree, and the ramification index is the order of the
inertia subgroup, which is trivial at an unramified prime. -/
theorem card_stabilizer_eq_inertiaDeg_of_notMem_ramifiedSet {K : Type} [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} (hp : p.Prime) (hpK : p ∉ ramifiedSet K) (P : Ideal (𝓞 K))
    [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card ↥(stabilizer Gal(K/ℚ) P) = (Ideal.span {(p : ℤ)}).inertiaDeg P := by
  have he : Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P = 1 := by
    rw [← card_inertia_eq_ramificationIdx_span hp P, inertia_eq_bot_of_notMem_ramifiedSet hp P hpK,
      Subgroup.card_bot]
  rw [card_stabilizer_eq_mul K hp P, he, one_mul]

end Unramified

/-! ### The relative residue degree inside the decomposition group -/

section Decomp

variable {k E : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
  [IsGalois k E]

/-- **The residue degree of a place over the place of the base below it divides the order of the
decomposition group there**, the decomposition group being the ramification index times the
residue degree. -/
theorem inertiaDeg_dvd_card_stabilizer_base (w : HeightOneSpectrum (𝓞 E)) :
    (primeUnder (𝓞 k) w).asIdeal.inertiaDeg w.asIdeal
      ∣ Nat.card ↥(stabilizer Gal(E/k) w.asIdeal) := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : w.asIdeal.IsMaximal := isMaximal_of_ne_bot_base w.asIdeal w.ne_bot
  haveI : w.asIdeal.LiesOver (primeUnder (𝓞 k) w).asIdeal := ⟨rfl⟩
  haveI : Algebra.IsSeparable (𝓞 k ⧸ (primeUnder (𝓞 k) w).asIdeal) (𝓞 E ⧸ w.asIdeal) :=
    isSeparable_residue_of_ne_bot_base (k := k) w.asIdeal w.ne_bot
  rw [Ideal.card_stabilizer_eq (G := Gal(E/k)) (primeUnder (𝓞 k) w).asIdeal
      (primeUnder (𝓞 k) w).ne_bot w.asIdeal,
    Ideal.inertiaDegIn_eq_inertiaDeg (primeUnder (𝓞 k) w).asIdeal w.asIdeal Gal(E/k)]
  exact Dvd.intro_left _ rfl

end Decomp

/-! ### Multiplicativity of the residue degree over the integers -/

section TowerDegree

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **The residue degree over the integers is multiplicative in a tower.**  The absolute norm of a
prime is the rational prime below raised to its residue degree over the integers, and also the
absolute norm of the prime below raised to the relative residue degree; the two expressions of the
same power of a prime have the same exponent. -/
theorem inertiaDeg_span_mul_of_under {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 k))
    (w : HeightOneSpectrum (𝓞 K)) (hvw : v.asIdeal = Ideal.under (𝓞 k) w.asIdeal)
    (hmem : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    (Ideal.span {(p : ℤ)}).inertiaDeg w.asIdeal
      = (Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal * v.asIdeal.inertiaDeg w.asIdeal := by
  haveI := liesOver_span_of_natCast_mem hp w hmem
  have hmemv : ((p : ℕ) : 𝓞 k) ∈ v.asIdeal := by
    rw [hvw, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  haveI := liesOver_span_of_natCast_mem hp v hmemv
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hvw⟩
  have h1 : Ideal.absNorm w.asIdeal = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg w.asIdeal) :=
    Ideal.absNorm_eq_pow_inertiaDeg' _ hp
  have h2 : Ideal.absNorm v.asIdeal = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal) :=
    Ideal.absNorm_eq_pow_inertiaDeg' _ hp
  have h3 : Ideal.absNorm w.asIdeal
      = Ideal.absNorm v.asIdeal ^ (v.asIdeal.inertiaDeg w.asIdeal) :=
    Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver _ _ v.isPrime v.ne_bot
  rw [h1, h2, ← pow_mul] at h3
  exact Nat.pow_right_injective hp.two_le h3

end TowerDegree

/-! ### Bounding the residue degree by the degree -/

section Bound

/-- **The residue degree of a place of a number field over the rational prime it contains is
positive and at most the degree of the field**, both being read off from the fundamental identity
relating ramification and residue degrees to the degree. -/
theorem inertiaDeg_span_pos_le_finrank {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    (Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal ≠ 0 ∧
      (Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal ≤ Module.finrank ℚ K := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  haveI := isMaximal_span_prime hp
  have hp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using Int.natCast_ne_zero.2 hp.ne_zero
  refine ⟨(Ideal.inertiaDeg_pos (R := ℤ) (S := 𝓞 K) (Ideal.span {(p : ℤ)}) v.asIdeal).ne', ?_⟩
  exact Ideal.inertiaDeg_le_finrank (R := ℤ) (S := 𝓞 K) (K := ℚ) (L := K)
    (p := Ideal.span {(p : ℤ)}) v.asIdeal hp0

end Bound

/-! ### The comparison -/

section Compare

variable {k F E : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra k E] [IsGalois k E] [Algebra F E]

/-- **The residue degree of an intermediate field divides the residue degree of the base times the
order of the decomposition group over the base.**  Both intermediate fields split the residue
degree of the place upstairs, and the relative residue degree over the base divides the order of
the decomposition group there. -/
theorem inertiaDeg_span_dvd_mul_card_stabilizer {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 E)) (hmem : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    (Ideal.span {(p : ℤ)}).inertiaDeg (primeUnder (𝓞 F) w).asIdeal
      ∣ (Ideal.span {(p : ℤ)}).inertiaDeg (primeUnder (𝓞 k) w).asIdeal
        * Nat.card ↥(stabilizer Gal(E/k) w.asIdeal) := by
  have hF := inertiaDeg_span_mul_of_under hp (primeUnder (𝓞 F) w) w rfl hmem
  have hk := inertiaDeg_span_mul_of_under hp (primeUnder (𝓞 k) w) w rfl hmem
  rw [hk] at hF
  refine dvd_trans (Dvd.intro _ hF.symm) ?_
  exact mul_dvd_mul_left _ (inertiaDeg_dvd_card_stabilizer_base w)

end Compare

/-! ### A divisibility of prime powers -/

section Arith

/-- A power of a prime dividing a product of a number and a power of the prime has its exponent
bounded by the sum of the two exponents, as soon as a bound on the multiplicity of the prime in
the number is known. -/
theorem le_add_of_pow_dvd_mul {ℓ a t m n : ℕ} (hℓ : ℓ.Prime) (hn : n ≠ 0)
    (hnt : ¬ ℓ ^ (t + 1) ∣ n) (hdvd : ℓ ^ a ∣ n * ℓ ^ m) : a ≤ t + m := by
  have hpow : (ℓ : ℕ) ^ m ≠ 0 := pow_ne_zero m hℓ.ne_zero
  have hne : n * ℓ ^ m ≠ 0 := mul_ne_zero hn hpow
  rw [hℓ.pow_dvd_iff_le_factorization hne, Nat.factorization_mul hn hpow] at hdvd
  have hle : n.factorization ℓ ≤ t := by
    by_contra hcon
    exact hnt ((hℓ.pow_dvd_iff_le_factorization hn).mpr (by omega))
  have hm : (ℓ ^ m).factorization ℓ = m := by
    rw [hℓ.factorization_pow]
    simp
  simp only [Finsupp.coe_add, Pi.add_apply, hm] at hdvd
  omega

end Arith

end InverseGalois.CFT
